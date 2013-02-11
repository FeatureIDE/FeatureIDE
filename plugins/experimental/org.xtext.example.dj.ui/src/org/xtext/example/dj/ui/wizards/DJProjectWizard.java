package org.xtext.example.dj.ui.wizards;

import static org.xtext.example.util.ValidationStatus.SYNTAX_ONLY;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchWizard;
import org.eclipse.ui.actions.WorkspaceModifyOperation;
import org.eclipse.xpand2.XpandExecutionContextImpl;
import org.eclipse.xpand2.XpandFacade;
import org.eclipse.xpand2.output.Outlet;
import org.eclipse.xpand2.output.OutputImpl;
import org.eclipse.xtend.typesystem.emf.EmfMetaModel;
import org.xtext.example.util.DJIdeProperties;
import org.xtext.example.util.ValidationStatus;

import ProjectGeneration.ProjectGenerationPackage;
import ProjectGeneration.ProjectSettings;

/**
 * This is a sample new wizard. Its role is to create a new file resource in the
 * provided container. If the container resource (a folder or a project) is
 * selected in the workspace when the wizard is opened, it will accept it as the
 * target container. The wizard creates one file with the extension "swrtj". If
 * a sample multi-page editor (also available as a template) is registered for
 * the same extension, it will be able to open it.
 */

public class DJProjectWizard extends Wizard implements INewWizard {
	private DJProjectWizardPage page;
	private ISelection selection;

	/**
	 * Constructor for DJProjectWizard.
	 */
	public DJProjectWizard() {
		super();
		setNeedsProgressMonitor(true);
	}

	/**
	 * Adding the page to the wizard.
	 */
	public void addPages() {
		page = new DJProjectWizardPage(selection, true);
		addPage(page);
	}

	/**
	 * This method is called when 'Finish' button is pressed in the wizard. We
	 * will create an operation and run it using wizard as execution context.
	 */
	public boolean performFinish() {
		final String containerName = page.getContainerName() + "/";
		final ProjectSettings settings = page.getSettings();
		IRunnableWithProgress op = new IRunnableWithProgress() {
			public void run(IProgressMonitor monitor)
					throws InvocationTargetException {
				try {
					new WorkspaceModifyOperation() {
						@Override
						protected void execute(IProgressMonitor monitor)
								throws CoreException,
								InvocationTargetException, InterruptedException {
							doFinish(containerName, settings, monitor);
						}
					}.run(monitor);
					ResourcesPlugin.getWorkspace().getRoot().refreshLocal(IProject.DEPTH_INFINITE, monitor);
				} catch (InterruptedException e) {
					e.printStackTrace();
				} catch (CoreException e) {
					e.printStackTrace();
				} finally {
					monitor.done();
				}
			}
		};
		try {
			getContainer().run(true, false, op);
		} catch (InterruptedException e) {
			return false;
		} catch (InvocationTargetException e) {
			Throwable realException = e.getTargetException();
			MessageDialog.openError(getShell(), "Error",
					realException.getMessage());
			return false;
		}
		return true;
	}

	/**
	 * The worker method. It will find the container, create the file if missing
	 * or just replace its contents, and open the editor on the newly created
	 * file.
	 */
	private void doFinish(String containerName, ProjectSettings settings,
			IProgressMonitor monitor) throws CoreException {
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();

		IProject project = root.getProject(containerName);
		project.create(monitor);
		project.open(monitor);

		final ValidationStatus marker = DJIdeProperties.getValidationStatus();
		DJIdeProperties.changeValidationStatus(SYNTAX_ONLY);

		IFile projFile = project.getFile(".project");
		projFile.delete(false, monitor);

		IFolder srcFolder = project.getFolder("src");
		srcFolder.create(false, false, monitor);
		IFolder srcGenFolder = project.getFolder("src-gen");
		srcGenFolder.create(false, false, monitor);

		String path = ResourcesPlugin.getWorkspace().getRoot().getLocation()
				.toOSString()
				+ project.getFullPath().toOSString() + "/";
		generateFiles(settings, path);

		DJIdeProperties.changeValidationStatus(marker);
	}

	@SuppressWarnings("unused")
	private void throwCoreException(String message) throws CoreException {
		IStatus status = new Status(IStatus.ERROR,
				"org.xtext.example.dj.ui", IStatus.OK, message, null);
		throw new CoreException(status);
	}

	/**
	 * We will accept the selection in the workbench to see if we can initialize
	 * from it.
	 * 
	 * @see IWorkbenchWizard#init(IWorkbench, IStructuredSelection)
	 */
	public void init(IWorkbench workbench, IStructuredSelection selection) {
		this.selection = selection;
	}

	/**
	 * Generates java project files.
	 * 
	 * @param settings
	 *            the project settings containing the specification of project
	 *            creation.
	 * @param path
	 *            the path in which create the project files.
	 */
	public static void generateFiles(ProjectSettings settings, String path) {
		OutputImpl output = new OutputImpl();
		output.addOutlet(new Outlet(false, "UTF-8", null, true, path));
		XpandExecutionContextImpl execCtx = new XpandExecutionContextImpl(
				output, null);
		execCtx.registerMetaModel(new EmfMetaModel(
				ProjectGenerationPackage.eINSTANCE));
		XpandFacade facade = XpandFacade.create(execCtx);
		facade.evaluate(
				"org::xtext::example::dj::ui::wizards::ProjectWizard::main",
				settings);
	}
}