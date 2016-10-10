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

import static de.ovgu.featureide.fm.core.localization.StringTable.CONTAINER_DOES_NOT_EXIST_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATING;
import static de.ovgu.featureide.fm.core.localization.StringTable.PATH_MUST_BE_SPECIFIED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.PATH_MUST_BE_VALID;
import static de.ovgu.featureide.fm.core.localization.StringTable.RESTRICTION;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.InvocationTargetException;
import java.net.URI;
import java.nio.charset.Charset;
import java.nio.file.CopyOption;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Stream;

import org.apache.tools.ant.util.FileUtils;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
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
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.fm.core.job.monitor.ProgressMonitor;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
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
        this("featureHouseImportPge", aWorkbench, selection);//$NON-NLS-1$
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
		
//		Composite composite = new Composite(parent, SWT.NULL);
//      composite.setLayout(new GridLayout());
//      composite.setLayoutData(new GridData(GridData.VERTICAL_ALIGN_FILL
//              | GridData.HORIZONTAL_ALIGN_FILL));
//      composite.setSize(composite.computeSize(SWT.DEFAULT, SWT.DEFAULT));
//      composite.setFont(parent.getFont());

      //createSourceGroup(composite);
      
     
		
//		Composite container = new Composite(parent, SWT.NULL);
//	    final GridLayout gridLayout = new GridLayout();
//	    gridLayout.numColumns = 1;
//	    container.setLayout(gridLayout);
	    //setControl(composite);
//	    
//	    
//	    //CheckButton TODO: AL Checkbutton only show configuration when checked
//	    checkButton = new Button(container, SWT.CHECK | SWT.RIGHT);
//	    checkButton.setText("Add existing FileSystem to Project");
//	    checkButton.addSelectionListener(new SelectionAdapter() {
//	    	
//		});
//	    
//	    Group toolGroup = new Group(container, SWT.NONE);
//		toolGroup.setText("File Selection");
//		toolGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
//		GridLayout projGridLayout = new GridLayout();
//		projGridLayout.numColumns = 2;
//		toolGroup.setLayout(projGridLayout);
//		
//		final Label helloLabel = new Label(toolGroup, SWT.NONE);
//		GridData gridData = new GridData(GridData.FILL_BOTH);
//		gridData.horizontalSpan = 2;
//		helloLabel.setLayoutData(gridData);
//		helloLabel.setText(PLEASE_SELECT_A_COMPOSER_FROM_THE_SELECTION_BELOW_);
//		
//	    Label label = new Label(toolGroup, SWT.NONE);
//	    label.setText("Composers:");
//	    toolCB = new Combo(toolGroup, SWT.READ_ONLY | SWT.DROP_DOWN);
//	    toolCB.setLayoutData(new GridData(GridData.FILL_BOTH));
//	    
//	    final Label descriptionLabel = new Label(toolGroup, SWT.NONE);
//	    GridData gridData2 = new GridData(GridData.FILL_BOTH);
//		gridData2.horizontalSpan = 2;
//	    descriptionLabel.setLayoutData(gridData2);
//	    
//	    StringBuilder descriptionStringBuilder = new StringBuilder();
//	    descriptionStringBuilder.append("Possible choices are:\n\n");
//	    List<IComposerExtension> composerExtensions = ComposerExtensionManager.getInstance().getComposers();
//	    extensions = new IComposerExtensionBase[composerExtensions.size()]; 
//	    composerExtensions.toArray(extensions);
//	    Arrays.sort(extensions, new Comparator<IComposerExtensionBase> () {
//			public int compare(IComposerExtensionBase arg0, IComposerExtensionBase arg1) {
//				return arg0.getName().compareTo(arg1.getName());
//			}
//	    });
//	    
//		for (IComposerExtensionBase composerExtension : extensions) {
////			descriptionStringBuilder.append(composerExtension.getName());
////			descriptionStringBuilder.append(": ");
////			descriptionStringBuilder.append(composerExtension.getDescription());
////			descriptionStringBuilder.append("\n");
//			toolCB.add(composerExtension.getName());
//		}
//		
////		String descriptionString = descriptionStringBuilder.toString();
//		if (composerExtensions.isEmpty()) {
////			descriptionString = NO_COMPOSITION_ENGINES_INSTALLED_;
////			setDescription(descriptionString);
//			toolCB.setEnabled(false);
//		}
////		descriptionLabel.setText(descriptionString);
//		toolCB.addModifyListener(new ModifyListener() {
//			public void modifyText(ModifyEvent e) {
//				composerExtension = extensions[toolCB.getSelectionIndex()];
//			}
//		});
//		toolCB.select(0);
//		
//		//Path Group Import File
//		importGroup = new Group(container, SWT.NONE);
//		layoutImportFile.numColumns =1;
//		layoutImportFile.verticalSpacing = 9;
//		importGroup.setText("Select FileSystem for Import");
//		//importGroup.setLayoutData(gd);
//		importGroup.setLayout(layoutImportFile);
//		
//		
//		
//		
//		//Path Group
//		pathGroup = new Group(container, SWT.NONE);
//		layout.numColumns = 2;
//		layout.verticalSpacing = 9;
//		pathGroup.setText("Path Specification:");
//		pathGroup.setLayoutData(gd);
//		pathGroup.setLayout(layout);
//		
//		String tooltip = SETS_THE_PATH_OF_COMPOSED_FILES_;
//		buildLabel = new Label(pathGroup, SWT.NULL);
//		buildLabel.setText("&Source Path:");
//		buildLabel.setToolTipText(tooltip);
//		buildPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
//		buildPath.setLayoutData(gd);
//		buildPath.setText("src");
//		buildPath.setToolTipText(tooltip);
//		
//		tooltip = SETS_THE_PATH_OF_FEATUREFOLDERS_;
//		label = new Label(pathGroup, SWT.NULL);
//		label.setText("&Feature Path:");
//		label.setToolTipText(tooltip);
//		sourcePath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
//		sourcePath.setLayoutData(gd);
//		sourcePath.setText(FEATURES);
//		sourcePath.setToolTipText(tooltip);
//		
//		tooltip = SETS_THE_PATH_OF_CONFIGURATIONFILES_;
//		label = new Label(pathGroup, SWT.NULL);
//		label.setText("&Configurations Path:");
//		label.setToolTipText(tooltip);
//		configsPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
//		configsPath.setLayoutData(gd);
//		configsPath.setText("configs");
//		configsPath.setToolTipText(tooltip);

		
		//addListeners();
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
		        
		        
		 Iterator resourcesEnum3 = super.getSelectedResources().iterator();
		 List<FileSystemElement> selectedFilesForImport2 = new ArrayList<FileSystemElement>();
		
		        while (resourcesEnum3.hasNext()) {
		            FileSystemElement thisFileElement2 = ((FileSystemElement) resourcesEnum3.next());
		            selectedFilesForImport2.add(thisFileElement2);       
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
		

		/*
		 * If a model file exists the model.xml can be created from it 
		 */
		if (modelFile != null) {

			IFeatureModel featureModel = null;

			URI locationUri = featureProject.getModelFile().getLocationURI();


			final GuidslFormat guidslFormat = new GuidslFormat();
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
			
		
				
				
				
				
			}
		
		for(FileSystemElement f: selectedFilesForImport2){
			
			if(f.getFileNameExtension().equals("features")){
				
				
				
				
				File file = (File) f.getFileSystemObject();		
				
				final IFolder configFolder = featureProject.getConfigFolder();
				final String fileName = file.getName();
				String name = fileName.replace(".features", ".config");
				
				
				
				
		
				try {
					doFinish(configFolder, name, file);
				} catch (CoreException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				
				selectedFilesForImport.remove(file);
				selectedFilesForImport.remove(modelFile);
//				final IRunnableWithProgress op = new IRunnableWithProgress() {
//					public void run(IProgressMonitor monitor) throws InvocationTargetException {
//						try {
//							doFinish(configFolder, fileName, monitor);
//						} catch (CoreException e) {
//							throw new InvocationTargetException(e);
//						} finally {
//							monitor.done();
//						}
//					}
//				};	
//				
//				try {
//					getContainer().run(true, false, op);
//				} catch (InterruptedException e) {
//					//return false;
//				} catch (InvocationTargetException e) {
//					Throwable realException = e.getTargetException();
//					MessageDialog.openError(getShell(), "Error", realException.getMessage());
//					//return false;
//				}
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

//		if (modelFile != null) {
//			IFolder folder = featureProject.getSourceFolder();
//			
//			List<IFeature> projectFeatures = new ArrayList<IFeature>();
//            for (IFeature feature : featureProject.getFeatureModel().getFeatures()) {
//            	projectFeatures.add(feature);		
//			}
//		
//			try {
//				for(IResource member: folder.members()){
//					if(!projectFeatures.contains(member)){
//						Path oldPath = (Path) member.getFullPath();
//						System.out.println("Location " + featureProject.getProject().getLocation());
//						System.out.println("Name" + featureProject.getProjectName());
//						System.out.println("Full Path" + featureProject.getProject().getFullPath());
//						System.out.println("RelativePath" + featureProject.getProject().getProjectRelativePath());
//						
//						Path newPath =  (Path) featureProject.getProject().getProjectRelativePath();
//					
////						CopyOption op = CopyOption.REPLACE_EXISTING; 
////						
////						
////						
////						Files.copy(oldPath, newPath, op);
////					
////						Files.move(oldPath, newPath, CopyOption.ATOMIC_MOVE );
//					}
//					
//					
//					
//				}
//			} catch (CoreException e) {
//
//				e.printStackTrace();
//			}
//
//			for (IFeature feature : featureProject.getFeatureModel().getFeatures()) {
//				
//			}

				
//		
//		}
		


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
	 * We will initialize file contents with a sample text.
	 */
	private InputStream openContentStream() {
		String contents = "";
		return new ByteArrayInputStream(contents.getBytes(Charset.availableCharsets().get("UTF-8")));
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
