package de.ovgu.featureide.ui.projectExplorer;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.internal.core.CompilationUnit;
import org.eclipse.jdt.internal.core.PackageFragment;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.projectExplorer.DrawImageForProjectExplorer.ExplorerObject;



/**
 * Labelprovider for projectExplorer - sets an image and a text before the files, folders and packages
 * 
 * @author Jonas Weigt
 */
@SuppressWarnings("restriction")
public class ProjectExplorerLabelProvider implements ILabelProvider {

	/*
	 * constant to create space for the image 
	 */
	private static final String SPACE_STRING = "             ";

	@Override
	public void addListener(ILabelProviderListener listener) {
	}

	@Override
	public void dispose() {
	}

	@Override
	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ILabelProvider#getImage(java.lang.Object)
	 * sets custom colored image instead of package, files or folders 
	 */
	@Override
	public Image getImage(Object element) {
		List<Integer> myColors = new ArrayList<Integer>();

		//returns the image for packages
		if (element instanceof PackageFragment) {
			PackageFragment frag = (PackageFragment) element;
			IFolder folder = (IFolder) frag.getResource();
			IFeatureProject featureProject = CorePlugin.getFeatureProject(frag.getParent().getResource());
			FSTModel model = featureProject.getFSTModel();
			if (model.getClasses().isEmpty()) {
				featureProject.getComposer().buildFSTModel();
				model = featureProject.getFSTModel();
			}
			IComposerExtensionClass composer = featureProject.getComposer();
			getPackageColors(folder, myColors, model, !composer.hasFeatureFolder());

			return DrawImageForProjectExplorer.drawExplorerImage(ExplorerObject.PACKAGE, myColors);

		}

		// returns the image for folders and preprocessor files
		if (element instanceof IResource) {
			IFeatureProject featureProject = CorePlugin.getFeatureProject((IResource) element);
			if (featureProject == null){
				return null;
			}
			IComposerExtensionClass composer = featureProject.getComposer();
			FSTModel model = featureProject.getFSTModel();
			if (model.getClasses().isEmpty()) {
				featureProject.getComposer().buildFSTModel();
				model = featureProject.getFSTModel();
			}
			//composer FeatureHouse
			if (composer.hasFeatureFolder() && element instanceof IFolder) {
				IFolder folder = (IFolder) element;
				//folder inSourceFolder but not SourceFolder itself
				if (folder.getParent().equals(featureProject.getSourceFolder())) {
					getFeatureFolderColors(folder, myColors, model);
					return DrawImageForProjectExplorer.drawFeatureHouseExplorerImage(myColors);
				}
			}

			//composer Preprocessor
			if (composer.hasSourceFolder() && !composer.hasFeatureFolder()) {
				if (element instanceof IFolder) {
					IFolder folder = (IFolder) element;
					if (isInSourceFolder(folder) && !folder.equals(featureProject.getSourceFolder())) {
						getPackageColors(folder, myColors, model, true);
						return DrawImageForProjectExplorer.drawExplorerImage(ExplorerObject.FOLDER, myColors);
					}
				}
				if (element instanceof IFile) {
					IFile file = (IFile) element;
					IContainer folder = file.getParent();
					if (folder instanceof IFolder) {
						if (isInSourceFolder((IFolder) folder)) {
							getPackageColors((IFolder)folder, myColors, model, true);
							return DrawImageForProjectExplorer.drawExplorerImage(ExplorerObject.FILE, myColors);
						}
					}
				}
			}
		}

		// returns the image for composed files
		if (element instanceof org.eclipse.jdt.internal.core.CompilationUnit) {

			CompilationUnit cu = (CompilationUnit) element;
			
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			IPath path = cu.getPath();
			IFile myfile = root.getFile(path);
			IFeatureProject featureProject = CorePlugin.getFeatureProject(myfile);
			FSTModel model = featureProject.getFSTModel();
			if (model.getClasses().isEmpty()) {
				featureProject.getComposer().buildFSTModel();
				model = featureProject.getFSTModel();
			}
			getColors(myColors, myfile, model, !featureProject.getComposer().hasFeatureFolder());

			return DrawImageForProjectExplorer.drawExplorerImage(ExplorerObject.FILE, myColors);
		}
		
		return null;
	}


	/**
	 * @param folder
	 * @param model
	 * @return color for featureFolders
	 */
	private void getFeatureFolderColors(IFolder folder, List<Integer> myColors, FSTModel model) {
		myColors.add(model.getFeature(folder.getName()).getColor());
	}

	/**
	 * @param myColors
	 * @param myfile
	 * @param model
	 * @param colorUnselectedFeature
	 * @return colors for files
	 */
	private void getColors(List<Integer> myColors, IFile myfile, FSTModel model, boolean colorUnselectedFeature) {
		FSTClass clazz = model.getClass(model.getAbsoluteClassName(myfile));
		if(clazz == null){
			return;
		}
		for (FSTRole r : clazz.getRoles()) {
			if (colorUnselectedFeature || r.getFeature().isSelected()) {
				if (r.getFeature().getColor() != -1) {
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
	private void getPackageColors(IFolder folder, List<Integer> myColors, FSTModel model, boolean colorUnselectedFeature) {
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
	 * @return if the Folder is in the Source Folder of the project
	 */
	private boolean isInSourceFolder(IFolder folder) {
		if (folder.equals(CorePlugin.getFeatureProject(folder).getSourceFolder())) {
			return true;
		}
		IContainer parent = folder.getParent();
		if (parent instanceof IFolder) {
			return isInSourceFolder((IFolder) parent);
		}
		return false;
	}

	
	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ILabelProvider#getText(java.lang.Object)
	 * sets customized text to have spacing for our image
	 */
	@Override
	public String getText(Object element) {

		//text for Packages
		if (element instanceof PackageFragment) {
			PackageFragment frag = (PackageFragment) element;
			IFeatureProject featureProject = CorePlugin.getFeatureProject(frag.getParent().getResource());
			if (featureProject == null) {
				return null;
			}
			String mytest = frag.getElementName();
			if (mytest.isEmpty()) {
				return SPACE_STRING + "(default package)";
			}
			return SPACE_STRING + mytest;	
		}

		//text for Folders
		if (element instanceof IResource) {
			IFeatureProject featureProject = CorePlugin.getFeatureProject((IResource) element);
			if (featureProject != null) {
				IComposerExtensionClass composer = featureProject.getComposer();
				//composer FeatureHouse Folder
				if (composer.hasFeatureFolder() && element instanceof IFolder) {

					IFolder folder = (IFolder) element;
					//folder inSourceFolder but not SourceFolder itself
					if (isInSourceFolder(folder) && !folder.equals(featureProject.getSourceFolder())) {
						return " " + folder.getName();
					}
				}
				//composer Preprocessor
				if (!composer.hasFeatureFolder()){
					if (element instanceof IFolder){
						IFolder folder = (IFolder) element;
						if (!folder.getName().equals("configs") && !folder.getName().equals("source")){
						return SPACE_STRING + folder.getName();
						}
					}
					if (element instanceof IFile){
						IFile file = (IFile) element;
						if (!file.getFileExtension().equals("xml") && !file.getFileExtension().equals("config")){
						return SPACE_STRING + file.getName();
						}
					}
				}
			}

		}
		
		//text for composed files
		if (element instanceof org.eclipse.jdt.internal.core.CompilationUnit) {

			CompilationUnit cu = (CompilationUnit) element;

			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
			IPath path = cu.getPath();
			IFile myfile = root.getFile(path);			
			return SPACE_STRING + myfile.getName();
			
		}

		return null;
	}

}
