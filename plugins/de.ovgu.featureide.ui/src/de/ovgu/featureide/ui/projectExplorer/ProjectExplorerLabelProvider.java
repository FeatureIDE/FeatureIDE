/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.projectExplorer;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.internal.core.CompilationUnit;
import org.eclipse.jdt.internal.core.PackageFragment;
import org.eclipse.jdt.internal.ui.packageview.PackageExplorerContentProvider;
import org.eclipse.jdt.internal.ui.packageview.PackageExplorerLabelProvider;
import org.eclipse.jface.viewers.StyledString;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.builder.IComposerExtensionClass.Mechanism;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.ui.projectExplorer.DrawImageForProjectExplorer.ExplorerObject;

/**
 * Label provider for projectExplorer - sets an image and a text before the files, folders and packages
 *
 * @author Jonas Weigt
 * @author Marcus Pinnecke
 */
@SuppressWarnings("restriction")
public class ProjectExplorerLabelProvider extends PackageExplorerLabelProvider {

	private List<String> selectedFeatures = new ArrayList<>();

	public ProjectExplorerLabelProvider() {
		super(new PackageExplorerContentProvider(true));
	}

	/*
	 * constant to create space for the image
	 */
	private static String SPACE_STRING = " ";

	@Override
	public Image getImage(Object element) {
		final Image superImage = super.getImage(element);
		final Set<Integer> elementColors = new HashSet<Integer>();

		// first returns the image for packages
		if (element instanceof PackageFragment) {
			final PackageFragment frag = (PackageFragment) element;
			final IResource fragmentRes = frag.getResource();
			if (!(fragmentRes instanceof IFolder)) {
				return superImage;
			}
			final IResource res = frag.getParent().getResource();
			if (res == null) {
				return superImage;
			}
			final IFeatureProject featureProject = CorePlugin.getFeatureProject(res);
			if (featureProject == null) {
				return superImage;
			}
			readCurrentConfiguration(featureProject);
			final IComposerExtensionClass composer = featureProject.getComposer();
			if (composer == null) {
				return superImage;
			}
			if (composer.getGenerationMechanism() == Mechanism.ASPECT_ORIENTED_PROGRAMMING) {
				return superImage;
			}
			FSTModel model = featureProject.getFSTModel();
			if ((model == null) || model.getClasses().isEmpty()) {
				composer.buildFSTModel();
				model = featureProject.getFSTModel();
				if (model == null) {
					return superImage;
				}
			}

			// Get current Package color
			getPackageColors((IFolder) fragmentRes, elementColors, model, hasUnselectedColors(composer));

			// Get all packages colors
			final Set<Integer> allPackageColors = new HashSet<Integer>();
			if (fragmentRes instanceof IFolder) {
				getAllPackageColors((IFolder) fragmentRes, allPackageColors, model, hasUnselectedColors(composer));
			}
			return DrawImageForProjectExplorer.drawExplorerImage(ExplorerObject.PACKAGE, new ArrayList<Integer>(elementColors),
					new ArrayList<Integer>(allPackageColors), superImage);
		} else if (element instanceof IResource) {
			final IResource res = (IResource) element;
			final IFeatureProject featureProject = CorePlugin.getFeatureProject(res);
			if (featureProject == null) {
				return superImage;
			}
			readCurrentConfiguration(featureProject);
			final IComposerExtensionClass composer = featureProject.getComposer();
			if (composer == null) {
				return superImage;
			}
			if (composer.getGenerationMechanism() == Mechanism.ASPECT_ORIENTED_PROGRAMMING) {
				return superImage;
			}
			FSTModel model = featureProject.getFSTModel();
			if ((model == null) || model.getClasses().isEmpty()) {
				composer.buildFSTModel();
				model = featureProject.getFSTModel();
				if (model == null) {
					return superImage;
				}
			}

			// Get color for the feature folder
			if (res instanceof IFolder) {
				final IFolder folder = (IFolder) res;
				if (composer.hasFeatureFolder() && isInFeatureFolder(folder)) {
					if (folder.getParent().equals(featureProject.getSourceFolder())) {
						getFeatureFolderColors(folder, elementColors, featureProject);
						return DrawImageForProjectExplorer.getFOPModuleImage(new ArrayList<Integer>(elementColors));
					} else if (isInSourceFolder(folder)) {
						return DrawImageForProjectExplorer.getPackageImage();
					}
				}
			}

			// Return folder package images for the source folder when working with munge composer
			if (composer.getName().equals("Munge")) {
				if (element instanceof IFile) {
					final IFile file = (IFile) element;
					if (isInMungeSource(file)) {
						getColors(elementColors, file, model, hasUnselectedColors(composer));
						return DrawImageForProjectExplorer.drawExplorerImage(ExplorerObject.FILE, new ArrayList<Integer>(elementColors), null, superImage);
					}
				}
				if ((element instanceof IFolder) && ((IFolder) element).getName().equals("source")) {
					final IFolder folder = (IFolder) element;
					getPackageColors(folder, elementColors, model, hasUnselectedColors(composer));
					return DrawImageForProjectExplorer.drawExplorerImage(ExplorerObject.PACKAGE, new ArrayList<Integer>(elementColors), null, superImage);
				}
			}

			Set<Integer> parentColors = null;
			// return images for composed files (.jak files)
			if (isInBuildFolder(res) && (res instanceof IFile) && isJavaFile((IFile) res)) {
				if (res.getParent() instanceof IFolder) {
					parentColors = new HashSet<Integer>();
					getAllPackageColors((IFolder) res.getParent(), parentColors, model, hasUnselectedColors(composer));
				}
				getColors(elementColors, (IFile) res, model, hasUnselectedColors(composer));
				return DrawImageForProjectExplorer.drawExplorerImage(ExplorerObject.JAVA_FILE, new ArrayList<Integer>(elementColors),
						new ArrayList<Integer>(parentColors), superImage);
			}
		} else if (element instanceof org.eclipse.jdt.internal.core.CompilationUnit) {
			// return images for compilation files
			final CompilationUnit cu = (CompilationUnit) element;
			final IFile myfile = (IFile) cu.getResource();
			final IFeatureProject featureProject = CorePlugin.getFeatureProject(myfile);
			if (featureProject == null) {
				return superImage;
			}
			FSTModel model = featureProject.getFSTModel();
			final IComposerExtensionClass composer = featureProject.getComposer();
			if (composer == null) {
				return superImage;
			}
			if (composer.getGenerationMechanism() == Mechanism.ASPECT_ORIENTED_PROGRAMMING) {
				return superImage;
			}
			if ((model == null) || model.getClasses().isEmpty()) {
				composer.buildFSTModel();
				model = featureProject.getFSTModel();
				if (model == null) {
					return superImage;
				}
			}
			Set<Integer> parentColors = null;
			if (cu.getParent() instanceof PackageFragment) {
				parentColors = new HashSet<Integer>();

				getAllPackageColors((IFolder) cu.getParent().getResource(), parentColors, model, hasUnselectedColors(composer));
			}
			getColors(elementColors, myfile, model, hasUnselectedColors(composer));

			return DrawImageForProjectExplorer.drawExplorerImage(ExplorerObject.JAVA_FILE, new ArrayList<Integer>(elementColors),
					new ArrayList<Integer>(parentColors), superImage);
		}
		return superImage;
	}

	/**
	 * Check if the given file is within munges "source" folder. Not the "src" folder.
	 *
	 * @param file The file to check
	 * @return true-When file is inside the munge source folder.
	 */
	private boolean isInMungeSource(IFile file) {
		IResource currentObject = file;
		while (currentObject.getParent() != null) {
			currentObject = currentObject.getParent();
			if (currentObject.getName().equals("source")) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Stores all selected Features in a string list.
	 *
	 * @param featureProject
	 *
	 * @deprecated TODO This should be included in {@link IFeatureProject}.
	 */
	@Deprecated
	private void readCurrentConfiguration(IFeatureProject featureProject) {
		final IFile currentConfiguration = featureProject.getCurrentConfiguration();
		if (currentConfiguration != null) {
			final ConfigurationManager instance = ConfigurationManager.getInstance(Paths.get(currentConfiguration.getLocationURI()),
					new Configuration(featureProject.getFeatureModel(), Configuration.PARAM_IGNOREABSTRACT | Configuration.PARAM_LAZY));
			selectedFeatures = (instance != null) ? new ArrayList<String>(instance.getObject().getSelectedFeatureNames()) : Collections.<String> emptyList();
		}
	}

	private boolean isJavaFile(final IFile file) {
		final String fileExtension = file.getFileExtension();
		if (fileExtension == null) {
			return false;
		}

		return fileExtension.equals("java") || fileExtension.equals("jak");
	}

	/**
	 * @param folder
	 * @param featureProject
	 * @return color for featureFolders
	 */
	private void getFeatureFolderColors(IFolder folder, Set<Integer> myColors, IFeatureProject featureProject) {
		final IFeature feature = featureProject.getFeatureModel().getFeature(folder.getName());
		myColors.add(FeatureColorManager.getColor(feature).getValue());
	}

	/**
	 * @param myColors
	 * @param myfile
	 * @param model
	 * @param colorUnselectedFeature
	 * @return colors for files
	 */
	private void getColors(Set<Integer> myColors, IFile myfile, FSTModel model, boolean colorUnselectedFeature) {
		if (model == null) {
			return;
		}
		String fileName = model.getAbsoluteClassName(myfile);
		if (model.getFeatureProject().getComposerID().equals("de.ovgu.featureide.composer.ahead")) {
			fileName = fileName.replace(".java", ".jak");
		}
		final FSTClass clazz = model.getClass(fileName);
		if (clazz == null) {
			return;
		}
		for (final FSTRole r : clazz.getRoles()) {
			if (colorUnselectedFeature || selectedFeatures.contains(r.getFeature().getName())) {
				if (r.getFeature().getColor() != FeatureColor.NO_COLOR.getValue()) {
					myColors.add(r.getFeature().getColor());
				}
			}
		}
	}

	/**
	 * @param folder
	 * @param colorUnselectedFeature
	 * @return colors for packages
	 */
	private void getPackageColors(IFolder folder, Set<Integer> myColors, FSTModel model, boolean colorUnselectedFeature) {
		try {
			for (final IResource member : folder.members()) {
				if (member instanceof IFile) {
					final IFile file = (IFile) member;
					getColors(myColors, file, model, colorUnselectedFeature);
				}
				if (member instanceof IFolder) {
					getPackageColors((IFolder) member, myColors, model, colorUnselectedFeature);
				}
			}
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}

	}

	/**
	 * @param folder
	 * @param colorUnselectedFeature
	 * @return colors for packages
	 */
	private void getAllPackageColors(IFolder folder, Set<Integer> allColors, FSTModel model, boolean colorUnselectedFeature) {
		// Check if default package
		if (folder.getName().equals("src")) {
			getPackageColors(folder, allColors, model, colorUnselectedFeature);
		} else {
			// Not default package
			if (folder.getParent() instanceof IFolder) {
				getPackageColors((IFolder) folder.getParent(), allColors, model, colorUnselectedFeature);
			}
		}

	}

	/**
	 * @param folder
	 * @return if the Folder is in the Source Folder of the project
	 */
	private boolean isInSourceFolder(IResource res) {
		return isInFolder(res, CorePlugin.getFeatureProject(res).getSourceFolder());
	}

	/**
	 *
	 * @param res folder to check
	 * @return if the folder is subdirectory of the feature folder
	 */
	private boolean isInFeatureFolder(IFolder res) {
		if (res.getParent() != null) {
			if (res.getParent() instanceof IFolder) {
				if (res.getParent().getName().equals("features")) {
					return true;
				} else {
					return false;
				}
			} else {
				return false;
			}
		}
		return false;
	}

	/**
	 * @param res
	 * @return if the Folder is in the build folder of the project
	 */
	private boolean isInBuildFolder(IResource res) {
		return isInFolder(res, CorePlugin.getFeatureProject(res).getBuildFolder());
	}

	private boolean isInFolder(IResource folder, IFolder parentFolder) {
		final IContainer parent = folder.getParent();
		if (parent.equals(parentFolder)) {
			return true;
		}
		if (parent instanceof IFolder) {
			return isInFolder(parent, parentFolder);
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jdt.internal.ui.packageview.PackageExplorerLabelProvider#getStyledText(java.lang.Object)
	 */
	@Override
	public StyledString getStyledText(Object element) {
		final String content = getText(element);
		if (content == null) {
			return super.getStyledText(element);
		}
		return new StyledString(content);

	}

	@Override
	public String getText(Object element) {
		final Set<Integer> elementColors = new HashSet<Integer>();
		SPACE_STRING = "";

		// text for Packages
		if (element instanceof PackageFragment) {
			final PackageFragment frag = (PackageFragment) element;
			final IResource parent = frag.getParent().getResource();
			if (parent == null) {
				return null;
			}
			final IFeatureProject featureProject = CorePlugin.getFeatureProject(parent);
			if (featureProject == null) {
				return null;
			}

			readCurrentConfiguration(featureProject);

			final IComposerExtensionClass composer = featureProject.getComposer();
			if (composer == null) {
				return null;
			}
			if (composer.getGenerationMechanism() == Mechanism.ASPECT_ORIENTED_PROGRAMMING) {
				return null;
			}
			final String elementName = frag.getElementName();

			getAllPackageColors((IFolder) frag.getResource(), elementColors, CorePlugin.getFeatureProject(frag.getResource()).getFSTModel(),
					hasUnselectedColors(composer));
			for (int i = 0; i < elementColors.size(); i++) {
				SPACE_STRING += " ";
			}

			if (elementColors.size() == 0) {
				SPACE_STRING = "";
			}

			if (elementName.isEmpty()) {
				return SPACE_STRING + "(default package)";
			}
			if (!isInBuildFolder(frag.getResource()) && !isInSourceFolder(frag.getResource())) {
				return null;
			}
			return SPACE_STRING + elementName;
		}

		else if (element instanceof IResource) {
			final IFeatureProject featureProject = CorePlugin.getFeatureProject((IResource) element);
			if (featureProject != null) {
				final IComposerExtensionClass composer = featureProject.getComposer();
				if (composer == null) {
					return null;
				}
				if (composer.getGenerationMechanism() == Mechanism.ASPECT_ORIENTED_PROGRAMMING) {
					return null;
				}

				final IResource res = (IResource) element;

				if (isInSourceFolder(res) && (res instanceof IFile)) {
					if (isInSourceFolder(res) && composer.getName().equals("AHEAD")) {
						return res.getName();
					}
					final FSTModel model = featureProject.getFSTModel();
					getColors(elementColors, (IFile) res, model, hasUnselectedColors(composer));
					SPACE_STRING = "";
					for (int i = 0; i < elementColors.size(); i++) {
						SPACE_STRING += " ";
					}
					return SPACE_STRING + res.getName();
				} else if (isInBuildFolder(res) && (res instanceof IFile)) {
					final FSTModel model = featureProject.getFSTModel();
					getColors(elementColors, (IFile) res, model, hasUnselectedColors(composer));
					SPACE_STRING = "";
					for (int i = 0; i < elementColors.size(); i++) {
						SPACE_STRING += " ";
					}
					return SPACE_STRING + res.getName();
				}

				if (composer.hasFeatureFolder()) {
					if (element instanceof IFolder) {
						final IFolder folder = (IFolder) element;

						// folder inSourceFolder but not SourceFolder itself
						if (isInSourceFolder(folder) && folder.getParent().equals(featureProject.getSourceFolder())) {
							return " " + folder.getName();
						}
					}

				} else if (isInBuildFolder(res) || isInSourceFolder(res)) {
					return SPACE_STRING + res.getName();
				}

				// Return spaces for the source folder when working with munge composer
				if (composer.getName().equals("Munge")) {
					final FSTModel model = featureProject.getFSTModel();
					if ((model == null) || model.getClasses().isEmpty()) {
						return SPACE_STRING + res.getName();
					}
					// Return text for munge source folder
					if ((element instanceof IFolder) && ((IFolder) element).getName().equals("source")) {
						final IFolder folder = (IFolder) element;
						getPackageColors(folder, elementColors, model, true);
						for (int i = 0; i < elementColors.size(); i++) {
							SPACE_STRING += " ";
						}
						return SPACE_STRING + res.getName();
					}
					if (element instanceof IFile) {
						final IFile file = (IFile) element;
						if (isInMungeSource(file)) {
							getColors(elementColors, file, model, hasUnselectedColors(composer));
							for (int i = 0; i < elementColors.size(); i++) {
								SPACE_STRING += " ";
							}
							return SPACE_STRING + res.getName();
						}
					}
				}

			}

		}

		// text for composed files
		else if (element instanceof org.eclipse.jdt.internal.core.CompilationUnit) {
			final CompilationUnit cu = (CompilationUnit) element;
			final IResource myfile = cu.getResource();
			final IFeatureProject featureProject = CorePlugin.getFeatureProject(myfile);
			if (featureProject == null) {
				return null;
			}
			final IComposerExtensionClass composer = featureProject.getComposer();
			if (composer == null) {
				return null;
			}
			if (composer.getGenerationMechanism() == Mechanism.ASPECT_ORIENTED_PROGRAMMING) {
				return null;
			}

			if (cu.getParent() instanceof PackageFragment) {
				final PackageFragment parent = (PackageFragment) cu.getParent();
				getAllPackageColors((IFolder) parent.getResource(), elementColors, CorePlugin.getFeatureProject(parent.getResource()).getFSTModel(),
						hasUnselectedColors(composer));
			} else {
				getColors(elementColors, (IFile) myfile, featureProject.getFSTModel(), hasUnselectedColors(composer));
			}
			for (int i = 0; i < elementColors.size(); i++) {
				SPACE_STRING += " ";
			}

			if (elementColors.size() == 0) {
				SPACE_STRING = "";
			}

			return SPACE_STRING + myfile.getName();

		}

		return null;
	}

	private boolean hasUnselectedColors(IComposerExtensionClass composer) {
		return (!composer.hasFeatureFolder() && !composer.hasSourceFolder()) || (composer.getGenerationMechanism() == Mechanism.PREPROCESSOR)
			|| composer.getName().equals("Munge");
	}

}
