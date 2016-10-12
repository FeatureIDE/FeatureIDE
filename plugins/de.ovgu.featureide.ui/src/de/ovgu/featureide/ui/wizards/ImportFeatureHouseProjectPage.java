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
package de.ovgu.featureide.ui.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.PATH_MUST_BE_SPECIFIED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.PATH_MUST_BE_VALID;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.net.URI;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

//import org.apache.tools.ant.util.FileUtils;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.FileSystemElement;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.internal.ide.filesystem.FileSystemStructureProvider;
import org.eclipse.ui.internal.wizards.datatransfer.DataTransferMessages;
import org.eclipse.ui.internal.wizards.datatransfer.WizardFileSystemResourceImportPage1;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.wizards.datatransfer.ImportOperation;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionBase;
import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

/**
 * 
 * This class creates the import page for the {@link ImportFeatureHouseProjectWizard} and
 * also provides the import functions necessary to build the feature model corresponding to a given modelfile in guidslformat or to 
 * the file structure.
 * 
 * @author Anna-Liisa Ahola
 * @author Maximilian Homann
 */
@SuppressWarnings(RESTRICTION)
public class ImportFeatureHouseProjectPage extends WizardFileSystemResourceImportPage1 {
	
	private FileSystemStructureProvider fileSystemStructureProvider = new FileSystemStructureProvider();

    protected static final String SOURCE_EMPTY_MESSAGE = DataTransferMessages.FileImport_sourceEmpty;
	
	protected IComposerExtensionBase composerExtension = null;
	protected IComposerExtensionBase[] extensions = null;
	
	protected Text sourcePath;
	protected Text configsPath;
	protected Text buildPath;
	
	
	//Group for import File dialog
	private boolean canFlipToNextPage = true;
	
	private IStructuredSelection selection;

    /**
     *	Creates an instance of this class
     *
     * @param aWorkbench IWorkbench
     * @param selection IStructuredSelection
     */
    public ImportFeatureHouseProjectPage(IWorkbench aWorkbench,
            IStructuredSelection selection) {
        this("featureHouseImportPage", aWorkbench, selection);//$NON-NLS-1$
        this.selection = selection;
      //this.project = project;
      	setTitle("Select Filesystem for Import");
      	setDescription("Import existing FeatureHouse Project into workspace");
    }
	
	/**
	 * 
	 * @param name
	 * @param aworkbench
	 * @param selection
	 */
	protected ImportFeatureHouseProjectPage(String name, IWorkbench aworkbench, IStructuredSelection selection) {
		super(aworkbench, selection);
	}
	
	public void createControl(Composite parent) {
		super.createControl(parent);	
		
	}	

    /*
     * In this case there is no OptionsGroup needed
     * 
     * 
     * (non-Javadoc)
     * @see org.eclipse.ui.dialogs.WizardDataTransferPage#createOptionsGroup(org.eclipse.swt.widgets.Composite)
     */
    @Override
    protected void createOptionsGroup(Composite parent) {
    	return;
    }
	
	public IComposerExtensionBase getCompositionTool() {
		return composerExtension;
	}
	
	public boolean hasCompositionTool() {
		return composerExtension != null;
	}

	protected boolean isEnabled(Text text) {
		if (text.isEnabled() && text.isVisible()) {
			return true;
		}
		return false;
	}

	protected boolean isPathEmpty(String path, String name) {
		if (path.length() == 0) {
			updateStatus(name + PATH_MUST_BE_SPECIFIED_);
			canFlipToNextPage  = false;
			return true;
		}
		canFlipToNextPage  = true;
		return false;
	}
	
	protected boolean isInvalidPath(String path, String name) {
		if (path.contains("*")
				|| path.contains("?")
				|| path.startsWith(".")
				|| path.endsWith(".")
				|| path.contains("//")
				|| path.endsWith("/")
				|| path.endsWith("/")
				|| path.contains("/.")
				|| path.contains("./")
				|| path.contains("<")
				|| path.contains(">")
				|| path.contains("|")
				|| path.contains(""+'"')) {
			updateStatus(name + PATH_MUST_BE_VALID);
			return true;
		}
		return false;
	}
	
	protected void updateStatus(String message) {
		setErrorMessage(message);
		setPageComplete(message == null);
	}
	
	public String getSourcePath() {
		if (sourcePath.isEnabled()) {
			return sourcePath.getText();
		} else {
			return getBuildPath();
		}
	}
	
	public String getConfigPath() {
		return configsPath.isEnabled() ? configsPath.getText() : "";

	}
	
	public String getBuildPath() {
		return buildPath.getText();
	}

	public boolean canFlipToNextPage() {
		return this.canFlipToNextPage;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.WizardResourceImportPage#createSourceGroup(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	protected void createSourceGroup(Composite parent) {
		
//	    checkButton = new Button(parent, SWT.CHECK | SWT.RIGHT);
//	    checkButton.setText(ADD_EXISTING_FOLDERS);
//	    
//	    checkButton.addSelectionListener(new ImportFeatureHouseProjectHandler(parent));

	    super.createRootDirectoryGroup(parent);
        super.createFileSelectionGroup(parent);
        super.createButtonsGroup(parent);
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.WizardResourceImportPage#getFileProvider()
	 */
	@Override
	protected ITreeContentProvider getFileProvider() {
		return super.getFileProvider();
		
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.WizardResourceImportPage#getFolderProvider()
	 */
	@Override
	protected ITreeContentProvider getFolderProvider() {
		// TODO Auto-generated method stub
		return super.getFolderProvider();
	}	

	@SuppressWarnings({ "rawtypes" })
	@Override
	public boolean finish() {
		if (!ensureSourceIsValid()) {
			return false;
		}

		final IFeatureProject featureProject = CorePlugin.getFeatureProject(SelectionWrapper.init(selection, IResource.class).getNext());

		
		//In the Wizard selected resources for import
		Iterator selecetedRessources = super.getSelectedResources().iterator();
		List<FileSystemElement> selectedFilesForImport = new ArrayList<FileSystemElement>();

		while (selecetedRessources.hasNext()) {
			FileSystemElement fileElement = ((FileSystemElement) selecetedRessources.next());
			selectedFilesForImport.add(fileElement);
		}

		File modelFile = null;

		
		//Searches if their exists a .model or .m file in the for import selected file system
		for (FileSystemElement element : selectedFilesForImport) {
			if (element.getFileNameExtension().equals("m") || element.getFileNameExtension().equals("model")) {

				modelFile = (File) element.getFileSystemObject();

				selectedFilesForImport.remove(modelFile);

			}
		}
		
		IFeatureModel featureModel = null; 
		
		/*
		 * If a model file exists the model.xml can be created from it 
		 */
		if (modelFile != null) {
			//Formatter for converting a GuidslFile into a FeatureModel
			final GuidslFormat guidslFormat = new GuidslFormat();
			URI locationUriModelFile = featureProject.getModelFile().getLocationURI();
			featureModel = createFeatureModelFromGuidsl(modelFile, guidslFormat, featureModel);

			if (featureModel != null) {
				boolean status = false;
				status = loadandSaveFeatureModel(featureProject, modelFile, guidslFormat, featureModel, locationUriModelFile);

				if (status) {
					try {
						openFileInEditor(featureProject.getModelFile());
					} catch (PartInitException e) {
						FMUIPlugin.getDefault().logError(e);
					}
				}
			}
		}

		/*
		 * Searches for configuration files in the list of selected files for import
		 */
		for (FileSystemElement f : selectedFilesForImport) {
			if (f.getFileNameExtension().equals("features") || f.getFileNameExtension().equals("config")) {

				File configFile = (File) f.getFileSystemObject();
				final IFolder configFolder = featureProject.getConfigFolder();
				String configFileName = configFile.getName();

				//If the the configuration file has the name extension 'features', it will be replaced
				if (f.getFileNameExtension().equals("features")) {
					configFileName = configFileName.replace(".features", ".config");
				}
				
				try {
					doFinish(configFolder, configFileName, configFile);
					selectedFilesForImport.remove(configFile);
				} catch (CoreException e) {
					e.printStackTrace();
				}
			}
		}
	
		importFileSystem(selectedFilesForImport, featureProject);
				
		if (modelFile == null) {
			fillModelwithFeatures(featureProject, featureModel);
		}

		return true;
	}

	/**
	 * @param featureProject
	 * @param featureModel
	 */
	private void fillModelwithFeatures(final IFeatureProject featureProject, IFeatureModel featureModel) {
		if (featureModel == null) {
			featureModel = featureProject.getFeatureModel();
		}
		IFeature rootFeature = featureModel.getFeature("Root");
		
		//Remove default features
		for (IFeature feature: featureModel.getFeatures()) {
			featureModel.deleteFeature(feature);
		}
		if (rootFeature.getStructure().hasChildren()) {
			for (IFeatureStructure child: rootFeature.getStructure().getChildren()) {
				rootFeature.getStructure().removeChild(child);
			}
		}
		
		try {
			for (IResource member: featureProject.getSourceFolder().members()) {
				if (member.getType() == IResource.FOLDER) {
					IFeature newFeature = new Feature(featureModel, member.getName());
					newFeature.getStructure().setParent(featureModel.getStructure().getRoot());
					rootFeature.getStructure().addChild(newFeature.getStructure());
					featureModel.addFeature(newFeature);
				}
				
			}
			FileHandler.save(Paths.get(featureProject.getModelFile().getLocationURI()), featureModel, new XmlFeatureModelFormat());
			openFileInEditor(featureProject.getModelFile());				
		} catch (CoreException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Loads and Saved the model.xml 
	 * 
	 * @param featureProject
	 * @param modelFile
	 * @param guidslFormat
	 * @param featureModel
	 * @param locationUriModelFile
	 * @return false: if the model could not be loaded; true: if the model could be loaded and saved
	 */
	private boolean loadandSaveFeatureModel(final IFeatureProject featureProject, File modelFile, final GuidslFormat guidslFormat, IFeatureModel featureModel,
			URI locationUriModelFile) {
		
			final ProblemList errors = FileHandler.load(modelFile.toPath(), featureModel, guidslFormat).getErrors();
			if (!errors.isEmpty()) {
				final StringBuilder sb = new StringBuilder("Error while loading file: \n");
				for (Problem problem : errors) {
					sb.append("Line ");
					sb.append(problem.getLine());
					sb.append(": ");
					sb.append(problem.getMessage());
					sb.append("\n");
				}
				MessageDialog.openWarning(new Shell(), "Warning!", sb.toString());
				return false;
			} else {
				
				//Creates the model.xml file by converting the featureModel and saves the xml
				FileHandler.save(Paths.get(locationUriModelFile), featureModel, new XmlFeatureModelFormat());
				
				return true;
				
			}
		
	}

	/**
	 * Creates a FeatureModel from a Guidsl file
	 * 
	 * @param modelFile File in Guidslformat which should be converted into a FeatureModle
	 * @param guidslFormat 
	 * @param featureModel 
	 * @return IFeatureModel
	 */
	private IFeatureModel createFeatureModelFromGuidsl(File modelFile, final GuidslFormat guidslFormat, IFeatureModel featureModel) {
		try {
			
			featureModel = FMFactoryManager.getFactory(modelFile.getAbsolutePath(), guidslFormat).createFeatureModel();
		} catch (NoSuchExtensionException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return featureModel;
	}
	
	

	/**
	 * Opens the imported model in a new editor. If it is already open, the
	 * editor will be closed first.
	 * 
	 * @throws PartInitException
	 */
	private void openFileInEditor(IFile outputFile) throws PartInitException {
		final IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		final IEditorInput editorInput = new FileEditorInput(outputFile);
		final IEditorReference[] refs = page.getEditorReferences();
		for (int i = 0; i < refs.length; i++) {
			if (refs[i].getEditorInput().equals(editorInput)) {
				page.closeEditor(refs[i].getEditor(false), false);
				break;
			}

		}
		IDE.openEditor(page, outputFile);
	}
	
	private void doFinish(IContainer container, String fileName, File configFile) throws CoreException {
		// create a sample file
		//monitor.beginTask(CREATING + fileName, 2);
		
		final IFile file = container.getFile(new Path(fileName));
		try{
			FileInputStream fileInputStream = new FileInputStream(configFile);
			
			if(!file.exists()){
				file.create(fileInputStream, true, null);
				
			}
			fileInputStream.close();
		} catch (IOException e){
			e.printStackTrace();
		}
		
//		monitor.worked(1);
//		monitor.setTaskName("opening");
		
//		getShell().getDisplay().asyncExec(new Runnable() {
//			public void run() {
//				IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
//				try {
//					IDE.openEditor(page, file, true);
//				} catch (PartInitException e) {
//				}
//			}
//		});
//		monitor.worked(1);
				
		
	}
	
	
	

	/**
	 * Import the resources with extensions as specified by the user
	 * 
	 * @param fileSystemObjects
	 * @param featureProject
	 * @return true: if the import operation has been performed
	 */
	protected boolean importFileSystem(List<FileSystemElement> fileSystemObjects, IFeatureProject featureProject) {
		
		List<File> fileList = new ArrayList<File>();
		for(FileSystemElement element: fileSystemObjects){
			fileList.add((File)(element.getFileSystemObject()));
		}
		
		
		ImportOperation operation;
		

		File sourceDirectory = getSourceDirectory();

		IPath path = getContainerFullPath().append(featureProject.getSourceFolder().getName());

		operation = new ImportOperation(path, sourceDirectory, fileSystemStructureProvider, this, fileList);

		operation.setCreateContainerStructure(false);

		operation.setContext(getShell());
		return executeImportOperation(operation);
	}
    
    /**
     *	Execute the passed import operation.  Answer a boolean indicating success.
     */
    @Override
    protected boolean executeImportOperation(ImportOperation op) {
        //initializeOperation(op);

        try {
            getContainer().run(true, true, op);
        } catch (InterruptedException e) {
            return false;
        } catch (InvocationTargetException e) {
            displayErrorDialog(e.getTargetException());
            return false;
        }

        IStatus status = op.getStatus();
        if (!status.isOK()) {
            ErrorDialog
                    .openError(getContainer().getShell(), DataTransferMessages.FileImport_importProblems,
                            null, // no special message
                            status);
            return false;
        }

        return true;
    }
}
