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

import java.awt.List;
import java.util.ArrayList;
import java.util.HashSet;
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
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.ui.projectExplorer.DrawImageForProjectExplorer.ExplorerObject;

/**
 * Label provider for projectExplorer - sets an image and a text before the files, folders and packages
 * 
 * @author Jonas Weigt
 * @author Marcus Pinnecke
 */
@SuppressWarnings("restriction")
public class ProjectExplorerLabelProvider extends PackageExplorerLabelProvider {

	public ProjectExplorerLabelProvider() {
		super(new PackageExplorerContentProvider(true));
	}

	/*
	 * constant to create space for the image 
	 */
	private static String SPACE_STRING = " ";

	@Override
	public Image getImage(Object element) {
		Image superImage = super.getImage(element);
		Set<Integer> elementColors = new HashSet<Integer>();

		//returns the image for packages
		if (element instanceof PackageFragment) {
			PackageFragment frag = (PackageFragment) element;
			IResource fragmentRes = frag.getResource();
			if (!(fragmentRes instanceof IFolder)) {
				return superImage;
			}
			IResource res = frag.getParent().getResource();
			if (res == null) {
				return superImage;
			}
			IFeatureProject featureProject = CorePlugin.getFeatureProject(res);
			if (featureProject == null) {
				return superImage;
			}
			IComposerExtensionClass composer = featureProject.getComposer();
			if (composer == null) {
				return superImage;
			}
			if (composer.getGenerationMechanism() == Mechanism.ASPECT_ORIENTED_PROGRAMMING) {
				return superImage;
			}

			FSTModel model = featureProject.getFSTModel();
			if (model == null || model.getClasses().isEmpty()) {
				composer.buildFSTModel();
				model = featureProject.getFSTModel();
				if (model == null) {
					return superImage;
				}
			}

			if (!composer.getName().equals("AHEAD")) {
				//Get current Package color
				getPackageColors((IFolder) fragmentRes, elementColors, model, !composer.hasFeatureFolder() && !composer.hasSourceFolder());

				//Get all packages colors
				Set<Integer> allPackageColors = new HashSet<Integer>();
				if (fragmentRes instanceof IFolder) {
					getAllPackageColors((IFolder) fragmentRes, allPackageColors, model, !composer.hasFeatureFolder() && !composer.hasSourceFolder());
				}
				return DrawImageForProjectExplorer.drawExplorerImage(ExplorerObject.PACKAGE, new ArrayList<Integer>(elementColors),
						new ArrayList<Integer>(allPackageColors), superImage);
			}

		}

		// returns the image for folders and preprocessor files
		if (element instanceof IResource) {
			IFeatureProject featureProject = CorePlugin.getFeatureProject((IResource) element);
			if (featureProject == null) {
				return superImage;
			}
			IComposerExtensionClass composer = featureProject.getComposer();
			if (composer == null) {
				return superImage;
			}
			if (composer.getGenerationMechanism() == Mechanism.ASPECT_ORIENTED_PROGRAMMING) {
				return superImage;
			}
			FSTModel model = featureProject.getFSTModel();
			if (model == null || model.getClasses().isEmpty()) {
				featureProject.getComposer().buildFSTModel();
				model = featureProject.getFSTModel();
			}
			if (!composer.getName().equals("AHEAD")) {
				if (composer.hasFeatureFolder()) {
					if (element instanceof IFolder) {
						IFolder folder = (IFolder) element;
						//folder inSourceFolder but not SourceFolder itself
						if (folder.getParent().equals(featureProject.getSourceFolder())) {
							getFeatureFolderColors(folder, elementColors, featureProject);
							return DrawImageForProjectExplorer.getFOPModuleImage(new ArrayList<Integer>(elementColors));
						} else if (isInSourceFolder(folder)) {
							return DrawImageForProjectExplorer.getPackageImage();
						}
					}
				}

				if (composer.hasSourceFolder() && !composer.hasFeatureFolder()) {
					if (element instanceof IFolder) {
						IFolder folder = (IFolder) element;
						if (isInSourceFolder(folder) && !folder.equals(featureProject.getSourceFolder())) {
							getPackageColors(folder, elementColors, model, !composer.hasFeatureFolder() && !composer.hasSourceFolder());
							return DrawImageForProjectExplorer.drawExplorerImage(ExplorerObject.PACKAGE, new ArrayList<Integer>(elementColors), null,
									superImage);
						}
					}
					if (element instanceof IFile) {
						IFile file = (IFile) element;
						IContainer folder = file.getParent();
						if (folder instanceof IFolder) {
							if (isInSourceFolder(file)) {
								getPackageColors((IFolder) folder, elementColors, model, !composer.hasFeatureFolder() && !composer.hasSourceFolder());
								return DrawImageForProjectExplorer.drawExplorerImage(isJavaFile(file) ? ExplorerObject.JAVA_FILE : ExplorerObject.FILE,
										new ArrayList<Integer>(elementColors), null, superImage);
							}
						}
					}
				}
			}
		}

		// returns the image for composed files
		if (element instanceof org.eclipse.jdt.internal.core.CompilationUnit) {
			CompilationUnit cu = (CompilationUnit) element;
			IFile myfile = (IFile) cu.getResource();
			IFeatureProject featureProject = CorePlugin.getFeatureProject(myfile);
			if (featureProject == null) {
				return superImage;
			}
			FSTModel model = featureProject.getFSTModel();
			IComposerExtensionClass composer = featureProject.getComposer();
			if (composer == null) {
				return superImage;
			}
			if (composer.getGenerationMechanism() == Mechanism.ASPECT_ORIENTED_PROGRAMMING) {
				return superImage;
			}
			if (model == null || model.getClasses().isEmpty()) {
				composer.buildFSTModel();
				model = featureProject.getFSTModel();
				if (model == null) {
					return superImage;
				}
			}

			Set<Integer> parentColors = null;

			if (!composer.getName().equals("AHEAD")) {
				if (cu.getParent() instanceof PackageFragment) {
					parentColors = new HashSet<Integer>();
					getAllPackageColors((IFolder) cu.getParent().getResource(), parentColors, model, !composer.hasFeatureFolder() && !composer.hasSourceFolder());
				}
				getColors(elementColors, myfile, model, !composer.hasFeatureFolder() && !composer.hasSourceFolder());
				return DrawImageForProjectExplorer.drawExplorerImage(ExplorerObject.JAVA_FILE, new ArrayList<Integer>(elementColors),
						new ArrayList<Integer>(parentColors), superImage);
			}
		}

		return superImage;
	}

	private boolean isJavaFile(final IFile file) {
		final String fileExtension = file.getFileExtension();
		if (fileExtension == null)
			return false;

		return fileExtension.equals("java") || fileExtension.equals("jak");
	}

	/**
	 * @param folder
	 * @param featureProject
	 * @return color for featureFolders
	 */
	private void getFeatureFolderColors(IFolder folder, Set<Integer> myColors, IFeatureProject featureProject) {
		IFeature feature = featureProject.getFeatureModel().getFeature(folder.getName());
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
		FSTClass clazz = model.getClass(model.getAbsoluteClassName(myfile));
		if (clazz == null) {
			return;
		}
		for (FSTRole r : clazz.getRoles()) {
			if (colorUnselectedFeature || r.getFeature().isSelected()) {
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
			for (IResource member : folder.members()) {
				if (member instanceof IFile) {
					IFile file = (IFile) member;
					getColors(myColors, file, model, colorUnselectedFeature);
				}
				if (member instanceof IFolder) {
					getPackageColors((IFolder) member, myColors, model, colorUnselectedFeature);
				}
			}
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}

	}

	/**
	 * @param folder
	 * @param colorUnselectedFeature
	 * @return colors for packages
	 */
	private void getAllPackageColors(IFolder folder, Set<Integer> allColors, FSTModel model, boolean colorUnselectedFeature) {
		//Check if default package
		if (folder.getName().equals("src")) {
			getPackageColors(folder, allColors, model, colorUnselectedFeature);
		} else {
			//Not default package
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
	 * @param res
	 * @return if the Folder is in the build folder of the project
	 */
	private boolean isInBuildFolder(IResource res) {
		return isInFolder(res, CorePlugin.getFeatureProject(res).getBuildFolder());
	}

	private boolean isInFolder(IResource folder, IFolder parentFolder) {
		IContainer parent = folder.getParent();
		if (parent.equals(parentFolder)) {
			return true;
		}
		if (parent instanceof IFolder) {
			return isInFolder((IFolder) parent, parentFolder);
		}
		return false;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jdt.internal.ui.packageview.PackageExplorerLabelProvider#getStyledText(java.lang.Object)
	 */
	@Override
	public StyledString getStyledText(Object element) {
		String content = getText(element);
		if (content == null) {
			return super.getStyledText(element);
		}
		return new StyledString(content);

	}

	@Override
	public String getText(Object element) {
		Set<Integer> elementColors = new HashSet<Integer>();

		SPACE_STRING = " ";

		//text for Packages
		if (element instanceof PackageFragment) {
			PackageFragment frag = (PackageFragment) element;
			IResource parent = frag.getParent().getResource();
			if (parent == null) {
				return null;
			}
			IFeatureProject featureProject = CorePlugin.getFeatureProject(parent);
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
			String elementName = frag.getElementName();

			if (!composer.getName().equals("AHEAD")) {
				getAllPackageColors((IFolder) frag.getResource(), elementColors, CorePlugin.getFeatureProject(frag.getResource()).getFSTModel(),
						!composer.hasFeatureFolder() && !composer.hasSourceFolder());
				for (int i = 0; i < elementColors.size(); i++)
					SPACE_STRING += " ";
			}

			if (elementColors.size() == 0)
				SPACE_STRING = "";

			if (elementName.isEmpty()) {
				return SPACE_STRING + "(default package)";
			}
			if (!isInBuildFolder(frag.getResource()) && !isInSourceFolder(frag.getResource())) {
				return null;
			}
			return SPACE_STRING + elementName;
		}

		//text for Folders
		else if (element instanceof IResource) {
			IFeatureProject featureProject = CorePlugin.getFeatureProject((IResource) element);
			if (featureProject != null) {
				IComposerExtensionClass composer = featureProject.getComposer();
				if (composer == null) {
					return null;
				}
				if (composer.getGenerationMechanism() == Mechanism.ASPECT_ORIENTED_PROGRAMMING) {
					return null;
				}
				IResource res = (IResource) element;

				if (composer.hasFeatureFolder()) {
					if (element instanceof IFolder) {
						IFolder folder = (IFolder) element;

						//folder inSourceFolder but not SourceFolder itself
						if (isInSourceFolder(folder) && folder.getParent().equals(featureProject.getSourceFolder())) {
							return " " + folder.getName();
						}
					}
				} else if (isInBuildFolder(res) || isInSourceFolder(res)) {
					return SPACE_STRING + res.getName();
				}
			}

		}

		//text for composed files
		else if (element instanceof org.eclipse.jdt.internal.core.CompilationUnit) {
			CompilationUnit cu = (CompilationUnit) element;
			IResource myfile = cu.getResource();
			IFeatureProject featureProject = CorePlugin.getFeatureProject(myfile);
			if (featureProject == null) {
				return null;
			}
			IComposerExtensionClass composer = featureProject.getComposer();
			if (composer == null) {
				return null;
			}
			if (composer.getGenerationMechanism() == Mechanism.ASPECT_ORIENTED_PROGRAMMING) {
				return null;
			}

			if (!composer.getName().equals("AHEAD")) {
				if (cu.getParent() instanceof PackageFragment) {
					PackageFragment parent = (PackageFragment) cu.getParent();
					getAllPackageColors((IFolder) parent.getResource(), elementColors, CorePlugin.getFeatureProject(parent.getResource()).getFSTModel(),
							!composer.hasFeatureFolder() && !composer.hasSourceFolder());
				} else
					getColors(elementColors, (IFile) myfile, featureProject.getFSTModel(), !composer.hasFeatureFolder() && !composer.hasSourceFolder());

			}
			for (int i = 0; i < elementColors.size(); i++)
				SPACE_STRING += " ";

			if (elementColors.size() == 0)
				SPACE_STRING = "";

			return SPACE_STRING + myfile.getName();

		}

		return null;
	}

}
