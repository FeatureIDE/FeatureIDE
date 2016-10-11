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
import java.lang.reflect.InvocationTargetException;
import java.net.URI;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Button;
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
import de.ovgu.featureide.fm.core.base.impl.AFeature;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.CreateFeatureBelowOperation;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;
import de.ovgu.featureide.ui.handlers.ImportFeatureHouseProjectHandler;

/**
 * TODO description
 * 
 * @author Anna-Liisa Ahola
 * @author Maximilian Homann
 */
@SuppressWarnings(RESTRICTION)
public class ImportFeatureHouseProjectPage extends WizardFileSystemResourceImportPage1 {
	
	private FileSystemStructureProvider fileSystemStructureProvider = new FileSystemStructureProvider();

    protected static final String SOURCE_EMPTY_MESSAGE = DataTransferMessages.FileImport_sourceEmpty;
	private static final String ADD_EXISTING_FOLDERS = "Add existing folders to selected project";
	protected IComposerExtensionBase composerExtension = null;
	protected IComposerExtensionBase[] extensions = null;
	
	protected Text sourcePath;
	protected Text configsPath;
	protected Text buildPath;
	
	private Button checkButton;
	
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
      	setTitle("Select FileSystem for Import");
      	setDescription("Import FeatureHouse Project into JavaProject");
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
		//CheckButton TODO: Max Checkbutton only show configuration when checked
	    checkButton = new Button(parent, SWT.CHECK | SWT.RIGHT);
	    checkButton.setText(ADD_EXISTING_FOLDERS);
	    
	    checkButton.addSelectionListener(new ImportFeatureHouseProjectHandler(parent));

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

		Iterator resourcesEnum = super.getSelectedResources().iterator();
		
		
		//List fileSystemObjects = new ArrayList();
		
		
		Iterator resourcesEnum2 = super.getSelectedResources().iterator();
		List<File> selectedFilesForImport = new ArrayList<File>();

		        while (resourcesEnum2.hasNext()) {
		            File thisFileElement = (File) ((FileSystemElement) (resourcesEnum2.next())).getFileSystemObject();
		            selectedFilesForImport.add(thisFileElement);       
		        }
		        
		       

		//        while (resourcesEnum.hasNext()) {
		//            fileSystemObjects.add(((FileSystemElement) resourcesEnum.next())
		//                    .getFileSystemObject());
		//            
		//        }

		//      while (resourcesEnum.hasNext()) {
		//      if(((FileSystemElement) resourcesEnum.next()).getFileNameExtension().equals("model")){
		//    	  String path = ((FileSystemElement) resourcesEnum).
		//    	  
		//      }

		//List<FileSystemElement> files = new ArrayList<FileSystemElement>();

		File modelFile = null;

		while (resourcesEnum.hasNext()) {
			
			FileSystemElement element = (FileSystemElement) resourcesEnum.next();

			if (element.getFileNameExtension().equals("m") || element.getFileNameExtension().equals("model")) {

				modelFile = (File) element.getFileSystemObject();

				resourcesEnum.remove();
				
				break;

			}
		}
		
		
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(SelectionWrapper.init(selection, IResource.class).getNext());
		IFeatureModel featureModel = null; 
		
		/*
		 * If a model file exists the model.xml can be created from it 
		 */
		if (modelFile != null) {
			final GuidslFormat guidslFormat = new GuidslFormat();
			URI locationUri = featureProject.getModelFile().getLocationURI();
			try {
				featureModel = FMFactoryManager.getFactory(modelFile.getAbsolutePath(), guidslFormat).createFeatureModel();
			} catch (NoSuchExtensionException e) {
				FMCorePlugin.getDefault().logError(e);
			}

			if (featureModel != null) {
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
				} else {
					FileHandler.save(Paths.get(locationUri), featureModel, new XmlFeatureModelFormat());
					try {
						openFileInEditor(featureProject.getModelFile());
					} catch (PartInitException e) {
						FMUIPlugin.getDefault().logError(e);
					}
				}
			}
			
//			IProject project = null;
//			final IResource res = SelectionWrapper.init(selection, IResource.class).getNext();
//			if (res != null) {
//				project = res.getProject();
//
//				try {
//
//					project.close(null);
//					project.open(null);
//
//				} catch (CoreException e) {
//
//					e.printStackTrace();
//				}
//
//			}
			

		}
		
		importFileSystem(selectedFilesForImport, featureProject);
		
		if (modelFile == null) {
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
		return true;
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
	
	/**
     *  Import the resources with extensions as specified by the user
     */
    protected boolean importFileSystem(List fileSystemObjects, IFeatureProject featureProject) {
        ImportOperation operation;

		//File sourceDirectory = getSourceDirectory();
        File sourceDirectory = getSourceDirectory();
        
		

//        if (shouldImportTopLevelFoldersRecursively)
//            operation = new ImportOperation(getContainerFullPath(),
//                    sourceDirectory, fileSystemStructureProvider,
//                    this, Arrays.asList(new File[] {getSourceDirectory()}));
        //else
      
        System.out.println(sourceDirectory);
        
        
        IPath path = getContainerFullPath().append(featureProject.getSourceFolder().getName());
        System.out.println(path);
        
        	operation = new ImportOperation(path,
                sourceDirectory, fileSystemStructureProvider,
                this, fileSystemObjects);
        	
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
