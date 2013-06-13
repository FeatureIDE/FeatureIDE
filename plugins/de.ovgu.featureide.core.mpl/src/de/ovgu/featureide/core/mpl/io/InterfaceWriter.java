/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.mpl.io;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.mpl.JavaInterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.constants.IOConstants;
import de.ovgu.featureide.core.mpl.signature.FeatureRoles;
import de.ovgu.featureide.core.mpl.signature.ProjectSignature;
import de.ovgu.featureide.core.mpl.signature.RoleMap;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractRole;
import de.ovgu.featureide.core.mpl.util.NumberConverter;
import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;

/** 
 * Writes different types of interface files.
 * 
 * @author Sebastian Krieter
 */
public class InterfaceWriter extends AbstractWriter {
	
	private abstract class MonitorJob extends Job {
		private static final int maxRelativeWork = 100;
		
		protected IProgressMonitor monitor = null;
		private int relativeWorkDone, absoluteWorkDone, maxAbsoluteWork;
		
		public MonitorJob(String name) {
			this(name, Job.LONG);
		}
		
		public MonitorJob(String name, int priority) {
			super(name);
			setPriority(priority);
			schedule();
		}
		
		@Override
		public IStatus run(IProgressMonitor monitor) {
			this.monitor = monitor;
			relativeWorkDone = 0;
			absoluteWorkDone = 0;
			maxAbsoluteWork = 1;
			
			monitor.beginTask(getName(), maxRelativeWork);
			
			boolean ok = work();
			monitor.done();
			
			return ok ? Status.OK_STATUS : Status.CANCEL_STATUS;
		}
		
		protected void setMaxAbsoluteWork(int maxAbsoluteWork) {
			this.maxAbsoluteWork = maxAbsoluteWork;
		}

		protected void worked() {
			int nworked = (100 * ++absoluteWorkDone) / maxAbsoluteWork;
			if (nworked > relativeWorkDone) {
				monitor.worked(nworked - relativeWorkDone);
				relativeWorkDone = nworked;
			}
		}
		
		protected abstract boolean work();
	}
	
	private final class SignatureGroup implements Comparable<SignatureGroup> {
		private final int id;
		private final IFolder folder;
		private int size = 0;
		
		public SignatureGroup(int id, IFolder folder) {
			this.id = id;
			this.folder = folder;
		}
		
		public void addSig() {
			size++;
		}

		@Override
		public int compareTo(SignatureGroup otherSigGroup) {
			int dSize = size - otherSigGroup.size;
			return dSize != 0 ? dSize : otherSigGroup.id - id;
		}
	}	
	
	public InterfaceWriter(JavaInterfaceProject interfaceProject) {
		super(interfaceProject);
	}
	
//	public void extendeModlues() {
//		FeatureModel fm = interfaceProject.getFeatureModel();
//		Configuration startConfiguration = new Configuration(fm);
//		
//		for (Feature feature : fm.getConcreteFeatures()) {
//			String featureName = feature.getName();
//			Configuration curConfiguration = new Configuration(startConfiguration, startConfiguration.getFeatureModel(), true);
//			curConfiguration.setManual(featureName, Selection.SELECTED);
//			for (Feature feature2 : curConfiguration.getSelectedFeatures()) {
//				feature2.getName();
//			}
//		}
//	}
	
	public void buildConfigurationInterfaces() {
		new MonitorJob("Build Configuration Interfaces") {
			@Override
			protected boolean work() {
				monitor.subTask("Calculate Solutions");
				
				final LinkedList<List<String>> solutionList;
				try {
					solutionList = interfaceProject.getConfiguration().getSolutions(interfaceProject.getConfigLimit());
				} catch (TimeoutException e) {
					MPLPlugin.getDefault().logError(e);
					return false;
				}
				final int numberSolutions = solutionList.size();
				
				monitor.subTask("Generate Signatures");
				
				IFolder interfaceFolder = interfaceProject.getProjectReference().getFolder("configuration_interfaces");
				IFolder groupListFolder = interfaceFolder.getFolder("groups");
				try {
					if (interfaceFolder.exists()) {
						interfaceFolder.delete(true, null);
					}
					interfaceFolder.create(false, true, null);
					groupListFolder.create(false, true, null);
				} catch (CoreException e) {
					MPLPlugin.getDefault().logError(e);
					return false;
				}

				final HashMap<ProjectSignature, SignatureGroup> signatureMap = new HashMap<ProjectSignature, SignatureGroup>();
				final NumberConverter converter = new NumberConverter(numberSolutions);
				
				int solutionId = 0, groupId = 0;
				setMaxAbsoluteWork(numberSolutions);
				
				while (!solutionList.isEmpty()) {
					List<String> featureList = solutionList.remove();
					
					ProjectSignature sig = interfaceProject.getRoleMap().generateSignature(featureList, interfaceProject.getFilterViewTag());
					
					SignatureGroup sigGroup = signatureMap.get(sig);
					if (sigGroup == null) {
						sigGroup = new SignatureGroup(++groupId, groupListFolder.getFolder("interface_" + converter.convert(groupId)));
						signatureMap.put(sig, sigGroup);
					}
					
					sigGroup.addSig();
					IFolder groupFolder = sigGroup.folder;
					
					if (!groupFolder.exists()) {
						try {
							groupFolder.create(true, true, null);
						} catch (CoreException e) {
							MPLPlugin.getDefault().logError(e);
							return false;
						}
					}
					
					writeSolutionList(featureList, groupFolder.getFile("featureList_" + converter.convert(++solutionId) + IOConstants.EXTENSION_SOLUTION));
					worked();
				}
				
				SignatureGroup[] signatureArray = new SignatureGroup[signatureMap.size()];
				signatureMap.values().toArray(signatureArray);
				Arrays.sort(signatureArray);
				
				if (signatureArray.length > 0) {
					int curNumber = signatureArray[signatureArray.length - 1].size;
					int count = 0;
					final StringBuilder sb = new StringBuilder("Number of Solutions -> IDs");
					sb.append(LINE_SEPARATOR);
					sb.append(LINE_SEPARATOR);
					sb.append(curNumber);
					
					for (int i = signatureArray.length - 1; i >= 0; i--) {
						SignatureGroup sigGroup = signatureArray[i];
						if (curNumber > sigGroup.size) {
							curNumber = sigGroup.size;
							sb.append(LINE_SEPARATOR);
							sb.append("\tCount : ");
							sb.append(count);
							count = 0;
							sb.append(LINE_SEPARATOR);
							sb.append(curNumber);
						}
						sb.append(count++ == 0 ? ':' + LINE_SEPARATOR + "\tIDs   : " : ", ");
						sb.append(converter.convert(sigGroup.id));
					}

					sb.append(LINE_SEPARATOR);
					sb.append("\tCount : ");
					sb.append(count);
					
					writeToFile(interfaceFolder.getFile("NumberOfSolutions.txt"), sb.toString());
				}
				
				MPLPlugin.getDefault().logInfo("Built Configuration Interfaces: " + signatureMap.size() + " / " + numberSolutions);
				return true;
			}
		};
	}
	
	public void compareConfigurationInterfaces() {
		new MonitorJob("Compare Configuration Interfaces") {
			@Override
			protected boolean work() {
				monitor.subTask("Calculate Solutions");
				
				final int configLimit = interfaceProject.getConfigLimit();
				
				final LinkedList<List<String>> solutionList;
				try {
					solutionList = interfaceProject.getConfiguration().getSolutions(configLimit);
				} catch (TimeoutException e) {
					MPLPlugin.getDefault().logError(e);
					return false;
				}
				
				monitor.subTask("Generate Signatures");
				
				final HashSet<ProjectSignature> signatures = new HashSet<ProjectSignature>();
				
				final LinkedList<ProjectSignature> signaturesList = new LinkedList<ProjectSignature>();
				final LinkedList<Integer> groupIdList = new LinkedList<Integer>();
				
				final NumberConverter converter = new NumberConverter(solutionList.size());
				int groupId = 0;
				
				while (!solutionList.isEmpty()) {
					ProjectSignature sig = interfaceProject.getRoleMap().generateSignature(solutionList.remove(), interfaceProject.getFilterViewTag());
					if (signatures.add(sig)) {
						signaturesList.add(sig);
						groupIdList.add(++groupId);
					}
				}
				final int 
					numberSignatures = signatures.size(),
					numberCompares = (numberSignatures*(numberSignatures - 1)) >> 1;
				
				monitor.subTask("Compare Signatures");
				setMaxAbsoluteWork(numberCompares);
				
				final double[] compareValues = new double[numberCompares];
				int compareIndex = 0;
				
				while (!signaturesList.isEmpty()) {
					ProjectSignature sig = signaturesList.remove();
					for (ProjectSignature otherSig : signaturesList) {
						compareValues[compareIndex++] = sig.similarityTo(otherSig);
						worked();
					}	
				}
				
				final StringBuilder similarityQString = new StringBuilder();
				for (int id : groupIdList) {
					similarityQString.append(converter.convert(id));
					similarityQString.append(',');
				}
				similarityQString.deleteCharAt(similarityQString.length() - 1);
				similarityQString.append(LINE_SEPARATOR);

				for (int i = 0; i < numberSignatures; i++) {
					for (int j = 0; j < numberSignatures; j++) {
						if (i < j) {
							similarityQString.append(compareValues[getIndex(i, j, numberSignatures)]);
						} else if (i > j) {
							similarityQString.append(compareValues[getIndex(j, i, numberSignatures)]);
						} else {
							similarityQString.append("1.0");
						}
						similarityQString.append(',');
					}
					similarityQString.deleteCharAt(similarityQString.length() - 1);
					similarityQString.append(LINE_SEPARATOR);
				}
				writeToFile(interfaceProject.getProjectReference().getFile(IOConstants.FILENAME_COMPARE_MATRIX), similarityQString.toString());
				MPLPlugin.getDefault().logInfo("Compared " + numberSignatures + " different Interfaces");
				return true;
			}
		};
	}
	
	private int getIndex(int i, int j, int max) {
		return j + (i * max) - (((i + 3) * i) >> 1) - 1;
	}
	
	private void writeSolutionList(List<String> featureList, IFile outputFile) {
		final StringBuilder solutionString = new StringBuilder();
		for (String featureName : featureList) {
			solutionString.append(featureName);
			solutionString.append(LINE_SEPARATOR);
		}
		writeToFile(outputFile, solutionString.toString());
	}

	public void buildFeatureInterfaces() {
		buildFeatureInterfaces(true, MPLPlugin.WRAPPER_INTERFACES 
				? IOConstants.FOLDERNAME_WRAPPER_INTERFACES 
				: IOConstants.FOLDERNAME_FEATURE_INTERFACES, false);
	}
	
	public void buildAllFeatureInterfaces(boolean reduced) {
		buildFeatureInterfaces(true, IOConstants.FOLDERNAME_FEATURE_ROLES, reduced);
	}
	
	public void buildAllFeatureInterfaces(String folderName) {
		buildFeatureInterfaces(true, folderName, false);
	}
	
	public void buildFeatureInterfaces(final boolean all, final String foldername, final boolean reduced) {
		new MonitorJob("Build Feature Interfaces") {
			protected boolean work() {
				RoleMap roleMap;
				if (reduced) {
					roleMap = new RoleMap(interfaceProject.getRoleMap(), interfaceProject.getFilterViewTag());
				} else {
					roleMap = interfaceProject.getRoleMap();
				}
				List<SelectableFeature> features = interfaceProject.getConfiguration().getFeatures();

				IFolder folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), foldername);
				
				try {
					folder.delete(true, null);
				} catch (CoreException e) {
					MPLPlugin.getDefault().logError(e);
					return false;
				}
		
				setMaxAbsoluteWork(features.size());
				
				for (SelectableFeature feature : features) {
					if (all || feature.getSelection() != Selection.UNSELECTED) {
						FeatureRoles roles = roleMap.getRoles(feature.getName());
						if (roles != null) {
							for (AbstractRole role : roles) {
		
								String packagename = role.getSignature().getPackage();
								
								String path = foldername + "/" + feature.getName() +
									(MPLPlugin.WRAPPER_INTERFACES ? "__Wrapper" : "") + 
									(packagename.isEmpty() ? "" :"/" + packagename);
								
								folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), path);
		
								if (all) {
									writeToFile(folder.getFile(role.getSignature().getName() + IOConstants.EXTENSION_JAVA), role.toShortString());
								} else {
									writeToFile(folder.getFile(role.getSignature().getName() + IOConstants.EXTENSION_JAVA), role.toString());
								}
								
							}
						}
					}
					worked();
				}
				if (MPLPlugin.WRAPPER_INTERFACES) {
					dublicateFeatureModel(CorePlugin.createFolder(interfaceProject.getProjectReference(), foldername));
					MPLPlugin.getDefault().logInfo("Built Wrapper Interfaces");
					
					MPLPlugin.PRIVATE_METHODS = false;
					MPLPlugin.WRAPPER_INTERFACES = false;
					interfaceProject.refreshRoleMap();
				} else {
					if (all) {
//						interfaceProject.refreshRoleMap();
					} else {
						MPLPlugin.getDefault().logInfo("Built Feature Interfaces");
					}
				}
				
				return true;
			}
		};
	}
	
	private void dublicateFeatureModel(IFolder folder) {		
		FeatureModel fm = LocalFileLoader.loadFeatureModel(interfaceProject);
		fm.clone();
		Feature root = fm.getRoot();
		
		Feature newRoot = new Feature(fm, "_Wrapper__Root_");
		newRoot.addChild(root);
		fm.addFeature(newRoot);
		fm.setRoot(newRoot);
		
		dublicateFeatureModel_rec(fm, root, newRoot);
		
		new FeatureModelWriter().writeModel(fm, folder.getFile(IOConstants.FILENAME_MODEL));
	}
	
	private void dublicateFeatureModel_rec(FeatureModel fm, Feature orginalFeature, Feature wrapperParent) {
    	if (orginalFeature != null) {
    		LinkedList<Feature> children = orginalFeature.getChildren();
        	
    		Feature wrapperFeature = new Feature(fm, orginalFeature.getName() + "__Wrapper");
    		wrapperFeature.setMandatory(orginalFeature.isMandatory());
    		wrapperFeature.setAbstract(orginalFeature.isAbstract());
    		wrapperFeature.setHidden(orginalFeature.isHidden());
    		wrapperFeature.setMultiple(orginalFeature.isMultiple());
    		if (orginalFeature.isAnd()) {
    			wrapperFeature.setAnd();
    		} else if (orginalFeature.isOr()) {
    			wrapperFeature.setOr();
    		} else if (orginalFeature.isAlternative()) {
    			wrapperFeature.setAlternative();
	    	}
    		
    		fm.addFeature(wrapperFeature);
    		wrapperParent.addChild(wrapperFeature);
    		
    		Node node = new Implies(
    				new Literal(wrapperFeature.getName()), 
    				new Literal(orginalFeature.getName()));
    		
    		fm.addConstraint(new Constraint(fm, node));
    		
	    	Iterator<Feature> i = children.iterator();
	    	while (i.hasNext()) {
	    		dublicateFeatureModel_rec(fm ,i.next(), wrapperFeature);
	    	}
    	}    	
    }
}
