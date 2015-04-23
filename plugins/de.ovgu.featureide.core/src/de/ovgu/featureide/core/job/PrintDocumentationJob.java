/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.job;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass.Mechanism;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.ProjectStructure;
import de.ovgu.featureide.core.signature.base.AbstractClassFragment;
import de.ovgu.featureide.core.signature.documentation.ContextMerger;
import de.ovgu.featureide.core.signature.documentation.FeatureModuleMerger;
import de.ovgu.featureide.core.signature.documentation.VariantMerger;
import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentMerger;
import de.ovgu.featureide.core.signature.documentation.base.BlockTag;
import de.ovgu.featureide.core.signature.documentation.base.DocumentationBuilder;
import de.ovgu.featureide.core.signature.filter.ConstraintFilter;
import de.ovgu.featureide.core.signature.filter.FeatureFilter;
import de.ovgu.featureide.core.signature.filter.IFilter;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.io.IOConstants;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * This job generates Javadoc from the feature-aware comments in a selected location.
 * Subsequently it uses the Javadoc parser to generate the documentation.
 * 
 * @author Sebastian Krieter
 */
public class PrintDocumentationJob extends AProjectJob<PrintDocumentationJob.Arguments> {
	
	public static class Arguments extends JobArguments {
		private final String foldername, featureName;
		private final String[] options;
		
		private final ADocumentationCommentMerger merger;
		
		public Arguments(String foldername, String[] options, ADocumentationCommentMerger merger, String featureName) {
			super(Arguments.class);
			this.foldername = foldername;
			this.options = options;
			this.merger = merger;
			this.featureName = featureName;
		}
	}
	
	protected PrintDocumentationJob(Arguments arguments) {
		super("Build Documentation", arguments);
	}

	@Override
	protected boolean work() {		
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		if (featureProject == null) {
			CorePlugin.getDefault().logWarning(this.project.getName() + " is no FeatureIDE Project!");
		}
		
		if (!deleteOldFolder()) {
			return false;
		}
		
		final ProjectSignatures projectSignatures = featureProject.getProjectSignatures();
		if (projectSignatures == null) {
			CorePlugin.getDefault().logWarning("No signatures available!");
			return false;
		}

		final Collection<IFilter<?>> commentFilters = new LinkedList<>();
		final Collection<IFilter<?>> signatureFilters = new LinkedList<>();

		final int[] featureIDs = projectSignatures.getFeatureIDs();
		if (arguments.merger instanceof VariantMerger) {
			final Configuration conf = new Configuration(featureProject.getFeatureModel(),
					Configuration.PARAM_LAZY | Configuration.PARAM_IGNOREABSTRACT);
			try {
				final IFile file = featureProject.getCurrentConfiguration();
				new ConfigurationReader(conf).readFromFile(file);
			} catch (Exception e) {
				CorePlugin.getDefault().logError(e);
				return false;
			}
			final Collection<String> featureNames = conf.getSelectedFeatureNames();
			
			final int[] tempFeatureList = new int[featureNames.size()];
			int count = 0;
			for (String featureName : featureNames) {
				final int id = projectSignatures.getFeatureID(featureName);
				if (id >= 0) {
					tempFeatureList[count++] = id;
				}
			}
			final int[] validFeatureIDs = new int[count];
			
			// sort feature list
			int c = 0;
			for (int j = 0; j < count; j++) {
				int curId = tempFeatureList[j];
				for (int k = 0; k < featureIDs.length; k++) {
					if (curId == featureIDs[k]) {
						validFeatureIDs[c++] = curId;
						break;
					}
				}
			}

//			filters.add(new FeatureFilter(validFeatureIDs));
			final Node[] nodes = new Node[conf.getFeatures().size() + 1];
			nodes[0] = NodeCreator.createNodes(conf.getFeatureModel());
			int i = 1;
			for (SelectableFeature feature : conf.getFeatures()) {
				Selection selection = feature.getSelection();
				nodes[i++] = selection == Selection.UNDEFINED ? new Literal("true") : new Literal(feature.getFeature().getName(), feature.getSelection() == Selection.SELECTED);
			}
			signatureFilters.add(new ConstraintFilter(nodes));
			commentFilters.add(new ConstraintFilter(nodes));
			
			arguments.merger.setValidFeatureIDs(featureIDs.length, validFeatureIDs);
		} else if (arguments.merger instanceof ContextMerger) {
			
//			filters.add(new ContextFilter(arguments.featureName, projectSignatures));
			final Node[] nodes = new Node[2];
			nodes[0] = NodeCreator.createNodes(projectSignatures.getFeatureModel());
			nodes[1] = new Literal(arguments.featureName, true);
			signatureFilters.add(new ConstraintFilter(nodes));
			commentFilters.add(new ConstraintFilter(nodes));
			
			arguments.merger.setValidFeatureIDs(featureIDs.length, featureIDs);
		} else if (arguments.merger instanceof FeatureModuleMerger) {
			final int index = projectSignatures.getFeatureID(arguments.featureName);
			arguments.merger.setValidFeatureIDs(featureIDs.length, new int[]{index});
			
			if (featureProject.getComposer().getGenerationMechanism() == Mechanism.PREPROCESSOR) {
				final Node[] nodes = new Node[2];
				nodes[0] = NodeCreator.createNodes(projectSignatures.getFeatureModel());
				nodes[1] = new Literal(arguments.featureName, true);
				signatureFilters.add(new ConstraintFilter(nodes));
				commentFilters.add(new ConstraintFilter(nodes));

				commentFilters.add(new IFilter<BlockTag>() {
					@Override
					public boolean isValid(BlockTag object) {
						for (String featureName : object.getConstraint().getContainedFeatures()) {
							if (featureName.equals(arguments.featureName)) {
								return true;
							}
						};
						return false;
					}
				});
			} else {
				signatureFilters.add(new FeatureFilter(index));
				commentFilters.add(new FeatureFilter(index));
			}
		}
		
		final DocumentationBuilder builder = new DocumentationBuilder(featureProject);
		builder.build(arguments.merger, commentFilters);
		
		buildJavaDoc(projectSignatures.iterator(signatureFilters));
		
		return true;
	}

	protected String folderPath = null;
	
	private boolean deleteOldFolder() {
		final IFolder folder = CorePlugin.createFolder(this.project, arguments.foldername);
		folderPath = folder.getLocation().toOSString();
		
		try {
			folder.delete(true, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
			return false;
		}
		return true;
	}

	private void buildJavaDoc(final SignatureIterator it) {
		final String extFoldername = arguments.foldername + "/src/";
		
		CorePlugin.createFolder(this.project, extFoldername);
		
		final HashSet<String> packageSet = new HashSet<String>();
		final LinkedList<String> classList = new LinkedList<String>();
		final ProjectStructure structure = new ProjectStructure(it);
		final String docOutput = folderPath + "\\doc\\";
		final String srcOutput = folderPath + "\\src\\";
		
		workMonitor.setMaxAbsoluteWork(structure.getClasses().size() + 2);
		
		for (AbstractClassFragment javaClass : structure.getClasses()) {
			String packagename = javaClass.getSignature().getPackage();
			
			String path = extFoldername + packagename.replace('.', '/');
			
			if (packagename.isEmpty()) {
				classList.add(srcOutput + javaClass.getSignature().getName() + IOConstants.EXTENSION_JAVA);
			} else {
				packageSet.add(packagename);
			}
			
			final IFolder folder = CorePlugin.createFolder(project, path);
			IOConstants.writeToFile(
					folder.getFile(javaClass.getSignature().getName() + IOConstants.EXTENSION_JAVA),
					javaClass.toString());
			workMonitor.worked();
		}
		final IFolder folder = CorePlugin.createFolder(project, arguments.foldername + "/doc/");
		
		final int defaultArguments = 4;
		int numDefaultArguments = defaultArguments;
		String[] args0 = null, args1 = null;
		
		if (!classList.isEmpty()) {
			args0 = new String[classList.size()];
			classList.toArray(args0);
			numDefaultArguments += args0.length;
		}
		if (!packageSet.isEmpty()) {
			if (args0 == null) {
				args0 = new String[packageSet.size()];
				packageSet.toArray(args0);
			} else {
				args1 = new String[packageSet.size()];
				packageSet.toArray(args1);
			}
			numDefaultArguments += packageSet.size();
		}
		
		final String[] javadocargs;
		if (arguments.options != null && arguments.options.length > 0 && !arguments.options[0].isEmpty()) {
			javadocargs = new String[numDefaultArguments + arguments.options.length];
			System.arraycopy(arguments.options, 0, javadocargs, numDefaultArguments, arguments.options.length);
		} else {
			javadocargs = new String[numDefaultArguments];
		}
		javadocargs[0] = "-d"; 
		javadocargs[1] = docOutput;
		javadocargs[2] = "-sourcepath";
		javadocargs[3] = srcOutput;
		if (args0 != null) {
			System.arraycopy(args0, 0, javadocargs, defaultArguments, args0.length);
		} 
		if (args1 != null) {
			System.arraycopy(args1, 0, javadocargs, defaultArguments + args0.length, args1.length);
		}
		
		for (int j = 0; j < javadocargs.length; j++) {
			System.out.println(javadocargs[j]);
		}
		
		com.sun.tools.javadoc.Main.execute(javadocargs);
		workMonitor.worked();
		
		try {
			folder.refreshLocal(IFolder.DEPTH_INFINITE, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		workMonitor.worked();
		
		CorePlugin.getDefault().logInfo("Built Documentation");
	}
}
