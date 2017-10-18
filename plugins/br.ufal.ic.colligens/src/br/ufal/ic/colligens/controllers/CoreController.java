package br.ufal.ic.colligens.controllers;

import static de.ovgu.featureide.fm.core.localization.StringTable.ANALYZING_FILES;

import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
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

	private final ProjectExplorerController projectExplorerController;
	private TypeChef typeChef;
	private static IWorkbenchWindow window;

	public CoreController() {
		projectExplorerController = new ProjectExplorerController();
	}

	public void setWindow(IWorkbenchWindow window) {
		CoreController.window = window;
		projectExplorerController.setWindow(window);
	}

	public void setSelection(ISelection selection) {
		projectExplorerController.setSelection(selection);
	}

	/**
	 * Run the analysis and returns the results to view
	 */
	public void run() {

		typeChef = new TypeChef();

		final Job job = new Job(ANALYZING_FILES) {

			/*
			 * (non-Javadoc)
			 * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime .IProgressMonitor)
			 */
			@Override
			protected IStatus run(IProgressMonitor monitor) {

				typeChef.setMonitor(monitor);

				if (monitor.isCanceled()) {
					return Status.CANCEL_STATUS;
				}

				try {
					// checks files in ProjectExplorer or PackageExplorer
					projectExplorerController.run();

					if (monitor.isCanceled()) {
						return Status.CANCEL_STATUS;
					}

					final List<IResource> list = projectExplorerController.getList();

					// get files to analyze e run;
					typeChef.run(list);

					// returns the result to view
					syncWithPluginView();

					if (monitor.isCanceled()) {
						return Status.CANCEL_STATUS;
					}

				} catch (final TypeChefException e) {
					e.printStackTrace();
					return Status.CANCEL_STATUS;
				} catch (final ProjectExplorerException e) {
					e.printStackTrace();
					return Status.CANCEL_STATUS;
				} finally {

					monitor.done();

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

			@Override
			public void run() {

				final IViewPart view = window.getActivePage().findView(InvalidConfigurationsView.ID);
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
							MessageDialog.openInformation(window.getShell(), Colligens.PLUGIN_NAME, "This file was successfully verified!");
						}
					}
				}
			}
		});
	}

	public static IWorkbenchWindow getWindow() {
		return window;
	}
}
