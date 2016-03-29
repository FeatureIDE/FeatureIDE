/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.mpl.job;

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATED_INTERFACE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_INTERFACE;
import static de.ovgu.featureide.fm.core.localization.StringTable.INTERFACES;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.util.Collection;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.io.velvet.VelvetFeatureModelWriter;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * Create mpl interfaces.
 * 
 * @author Sebastian Krieter
 * @author Marcus Pinnecke (Feature Interface)
 */
public class CreateInterfaceJob extends AProjectJob<CreateInterfaceJob.Arguments> {
	
	public static class Arguments extends JobArguments {
		private final IFeatureProject featureProject;
		private final Collection<String> featureNames;
		
		public Arguments(IFeatureProject featureProject, Collection<String> featureNames) {
			super(Arguments.class);
			this.featureProject = featureProject;
			this.featureNames = featureNames;
		}
	}
	
	protected CreateInterfaceJob(Arguments arguments) {
		super(CREATE_INTERFACE, arguments);
	}

	@Override
	protected boolean work() {
		IFeatureModel newFeatureModel = createInterface(arguments.featureProject.getFeatureModel(), arguments.featureNames);

		String projectName = arguments.featureProject.getProjectName();
		String interfaceName = "I" + projectName;
		newFeatureModel.getStructure().getRoot().getFeature().setName(interfaceName);

		VelvetFeatureModelWriter modelWriter = new VelvetFeatureModelWriter(newFeatureModel, true);
		String interfaceContent = modelWriter.writeToString();

		try {
			// create interface
			IFolder mplFolder = project.getFolder(INTERFACES);
			if (!mplFolder.exists())
				mplFolder.create(true, true, null);

			IFile interfaceFile = mplFolder.getFile(interfaceName + ".velvet");

			// TODO: warning for existing interface file
			if (!interfaceFile.exists()) {
				ByteArrayInputStream interfaceContentStream = new ByteArrayInputStream(
						interfaceContent.getBytes());
				interfaceFile.create(interfaceContentStream, true, null);
				interfaceContentStream.close();
			} else {
				ByteArrayInputStream interfaceContentStream = new ByteArrayInputStream(
						interfaceContent.getBytes());
				interfaceFile.setContents(interfaceContentStream, true, false, null);
				interfaceContentStream.close();
			}
		} catch (CoreException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		MPLPlugin.getDefault().logInfo(CREATED_INTERFACE_);
		return true;
	}
	
	private IFeatureModel createInterface(IFeatureModel orgFeatureModel, Collection<String> selectedFeatureNames) {
		// Calculate Constraints
		IFeatureModel m = orgFeatureModel.clone(null);		
		for (IFeature feat : m.getFeatures()) {
			feat.getStructure().setAbstract(!selectedFeatureNames.contains(feat.getName()));
        }
		workMonitor.setMaxAbsoluteWork(3);
		Node nodes = NodeCreator.createNodes(m, false);
		workMonitor.worked();
		Node cnf = nodes.toCNF();
		workMonitor.worked();
		
		// Calculate Model
		m = orgFeatureModel.clone(null);
		
        // mark features
        for (IFeature feat : m.getFeatures()) {
            if (!selectedFeatureNames.contains(feat.getName())) {
                feat.setName(MARK1);
            }
        }
        
        IFeature root = m.getStructure().getRoot().getFeature();

        m.getStructure().setRoot(null);
        m.reset();
        
        // set new abstract root
        IFeature nroot = FMFactoryManager.getFactory().createFeature(m, "nroot");
        nroot.getStructure().setAbstract(true);
        nroot.getStructure().setAnd();
        nroot.getStructure().addChild(root.getStructure());
        root.getStructure().setParent(nroot.getStructure());
        
        // merge tree
    	cut(nroot);
        do {
        	changed = false;
            merge(nroot.getStructure(), GROUP_NO);
        } while (changed);
        
        int count = 0;
        Hashtable<String, IFeature> featureTable = new Hashtable<String, IFeature>();
        LinkedList<IFeature> featureStack = new LinkedList<IFeature>();
        featureStack.push(nroot);
        while (!featureStack.isEmpty()) {
        	IFeature curFeature = featureStack.pop();
        	for (IFeature feature : FeatureUtils.convertToFeatureList(curFeature.getStructure().getChildren())) {
				featureStack.push(feature);
			}
        	if (curFeature.getName().startsWith(MARK1)) {
        		curFeature.setName("_Abstract_" + count++);
        		curFeature.getStructure().setAbstract(true);
        	}
        	featureTable.put(curFeature.getName(), curFeature);
        }
        m.setFeatureTable(featureTable);
        m.getStructure().setRoot(nroot.getStructure());
        
        if (cnf instanceof And) {
        	final Node[] children = cnf.getChildren();
        	workMonitor.setMaxAbsoluteWork(children.length + 2);
//    		final SatSolver modelSatSolver = new SatSolver(NodeCreator.createNodes(m), 500);
        	for (int i = 0; i < children.length; i++) {
        		final Node child = children[i];
        		final Node notChild = new Not(child.clone());
        		SatSolver modelSatSolver = new SatSolver(new And(NodeCreator.createNodes(m), notChild), 1000);
        		try {
					if (modelSatSolver.isSatisfiable()) {
						m.addConstraint(FMFactoryManager.getFactory().createConstraint(m, child));
					}
				} catch (TimeoutException e) {
					MPLPlugin.getDefault().logError(e);
				} finally {
					workMonitor.worked();
				}
			}
        }
        return m;
    }

	private static final String MARK1 = "?", MARK2 = "??";
	
	private static final int
		GROUP_OR = 1, GROUP_AND = 2, GROUP_ALT = 3, GROUP_NO = 0;
	

	private boolean changed = false;
	
	private static int getGroup(IFeatureStructure f) {
		if (f == null) {
			return GROUP_NO;
		} else if (f.isAnd()) {
			return GROUP_AND;
		} else if (f.isOr()) {
			return GROUP_OR;
		} else {
			return GROUP_ALT;
		}
	}
	
	
	
	
	private void merge(IFeatureStructure curFeature, int parentGroup) {
        if (!curFeature.hasChildren()) {
        	return;
        }
        int curFeatureGroup = getGroup(curFeature);
		List<IFeatureStructure> list = curFeature.getChildren();
        for (IFeatureStructure child : list) {
            merge(child, curFeatureGroup);
	        curFeatureGroup = getGroup(curFeature);
		}
        
		if (curFeature.getFeature().getName().equals(MARK1)) {
			if (parentGroup == curFeatureGroup) {
				deleteFeature(curFeature);
			} else {
				switch (parentGroup) {
				case GROUP_AND:
					IFeatureStructure parent = curFeature.getParent();
					if (parent.getChildrenCount() == 1) {
						switch (curFeatureGroup) {
						case GROUP_OR:
							parent.setOr();
							break;
						case GROUP_ALT:
							parent.setAlternative();
							break;
						}
						deleteFeature(curFeature);
					}
					break;
				case GROUP_OR:
					if (curFeatureGroup == GROUP_AND) {
						boolean allOptional = true;
						for (IFeatureStructure child : list) {
							if (child.isMandatory()) {
								allOptional = false;
								break;
							}
						}
						if (allOptional) {
							deleteFeature(curFeature);
						}
					}
					break;
				case GROUP_ALT:
					if (curFeatureGroup == GROUP_AND && list.size() == 1) {
						deleteFeature(curFeature);
					}
					break;
				}
			}
		}
    }
	
	private void deleteFeature(IFeatureStructure curFeature) {
		IFeatureStructure parent = curFeature.getParent();
        List<IFeatureStructure> children = curFeature.getChildren();
		parent.removeChild(curFeature);
		changed = true;
		for (IFeatureStructure child : children) {
			parent.addChild(child);
		}
		children.clear();// XXX code smell
	}
	
	private static boolean cut(final IFeature curFeature) {
		final IFeatureStructure structure = curFeature.getStructure();
        boolean notSelected = curFeature.getName().equals(MARK1);
        
		List<IFeature> list = FeatureUtils.convertToFeatureList(structure.getChildren());
        if (list.isEmpty()) {
        	return notSelected;
        } else {
        	boolean[] remove = new boolean[list.size()];
        	int removeCount = 0;
        	
    		int i = 0;
    		for (IFeature child : list) {
    			remove[i++] = cut(child);
			}
            
        	// remove children
            Iterator<IFeature> it = list.iterator();
    		for (i = 0; i < remove.length; i++) {
                IFeature feat = it.next();
                if (remove[i]) {
                	it.remove();
                	feat.getStructure().setParent(null);
                	removeCount++;
//    				changed = true;
                }
            }
			if (list.isEmpty()) {
    			structure.setAnd();
				return notSelected;
    		} else {
    			switch (getGroup(structure)) {
    			case GROUP_OR:
    				if (removeCount > 0) {
    					structure.setAnd();
        				for (IFeature child : list) {
        	    			child.getStructure().setMandatory(false);
        				}
    				} else if (list.size() == 1) {
    					structure.setAnd();
        				for (IFeature child : list) {
        	    			child.getStructure().setMandatory(true);
        				}
    				}
    				break;
    			case GROUP_ALT:
    				if (removeCount > 0) {
    					if (list.size() == 1) {
        					structure.setAnd();
            				for (IFeature child : list) {
            	    			child.getStructure().setMandatory(false);
            				}
        				} else {
            				IFeature pseudoAlternative = FMFactoryManager.getFactory().createFeature(curFeature.getFeatureModel(), MARK2);
            				pseudoAlternative.getStructure().setMandatory(false);
            				pseudoAlternative.getStructure().setAlternative();
            				for (IFeature child : list) {
            					pseudoAlternative.getStructure().addChild(child.getStructure());
            				}
            				list.clear();
            				structure.setAnd();
            				structure.addChild(pseudoAlternative.getStructure());
        				}
    				} else if (list.size() == 1) {
    					structure.setAnd();
        				for (IFeature child : list) {
        	    			child.getStructure().setMandatory(true);
        				}
    				}
    				break;
    			}
    		}
        }
        return false;
    }
}
