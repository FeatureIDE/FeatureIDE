package br.ufal.ic.colligens.controllers;

import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchWindow;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.models.FileProxy;
import br.ufal.ic.colligens.models.TypeChef;
import br.ufal.ic.colligens.models.TypeChefException;
import br.ufal.ic.colligens.views.InvalidConfigurationsView;


/**
 * @author Thiago Emmanuel
 */
public class CoreController {
	private ProjectExplorerController projectExplorerController;
	private TypeChef typeChef;
	private static IWorkbenchWindow window;
	private static IProgressMonitor monitor;

	public CoreController() {
		projectExplorerController = new ProjectExplorerController();
	}

	public void setWindow(IWorkbenchWindow window) {
		CoreController.window = window;
		projectExplorerController.setWindow(window);
	}

	/**
	 * Run the analysis and returns the results to view
	 */
	public void run() {

		typeChef = new TypeChef();

		Job job = new Job("Analyzing files") {
			/*
			 * (non-Javadoc)
			 * 
			 * @see
			 * org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime
			 * .IProgressMonitor)
			 */
			protected IStatus run(IProgressMonitor monitor) {

				CoreController.monitor = monitor;

				if (monitor.isCanceled())
					return Status.CANCEL_STATUS;

				try {
					// checks files in ProjectExplorer or PackageExplorer
					projectExplorerController.run();

					if (monitor.isCanceled())
						return Status.CANCEL_STATUS;
					// get files to analyze e run
					typeChef.run(projectExplorerController.getList());

					// returns the result to view
					syncWithPluginView();

				} catch (TypeChefException e) {
					e.printStackTrace();
					return Status.CANCEL_STATUS;
				} catch (ProjectExplorerException e) {
					e.printStackTrace();
					return Status.CANCEL_STATUS;
				} finally {

					monitor.done();
					CoreController.monitor = null;

				}

				return Status.OK_STATUS;
			}
		};

		job.setUser(true);
		job.schedule();

	}

	/**
	 * returns the result to view
	 */
	private void syncWithPluginView() {
		Display.getDefault().asyncExec(new Runnable() {
			public void run() {

				IViewPart view = window.getActivePage().findView(
						InvalidConfigurationsView.ID);
				if (view instanceof InvalidConfigurationsView) {
					final InvalidConfigurationsView analyzerView = (InvalidConfigurationsView) view;

					// Typechef checks performed at least one analysis
					if (typeChef.isFinish()) {
						// get list of error logs
						List<FileProxy> logs;
						logs = typeChef.getFilesLog();
						// returns the list to view
						analyzerView.setInput(logs);
						//
						if (logs.isEmpty()) {
							MessageDialog.openInformation(window.getShell(),
									Colligens.PLUGIN_NAME,
									"This file was successfully verified!");
						}
					}
				}
			}
		});
	}

	public static IWorkbenchWindow getWindow() {
		return window;
	}

	public static boolean isCanceled() {
		return monitor != null ? CoreController.monitor.isCanceled() : false;
	}

	public static void monitorWorked(int value) {
		if (monitor == null)
			return;
		monitor.worked(value);
	}

	public static void monitorSubTask(String label) {
		if (monitor == null)
			return;
		monitor.subTask(label);
	}

	public static void monitorBeginTask(String label, int value) {
		if (monitor == null)
			return;
		monitor.beginTask(label, value);
	}
}
