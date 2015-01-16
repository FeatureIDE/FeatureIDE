package de.ovgu.featureide.ui.actions;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;
import de.ovgu.featureide.ui.actions.generator.IConfigurationBuilderBasics.BuildOrder;
import de.ovgu.featureide.ui.actions.generator.IConfigurationBuilderBasics.BuildType;


public class TestAction implements IWorkbenchWindowActionDelegate {

	private ISelection selection;
	
	@Override
	public void run(IAction action) {
		if (selection instanceof StructuredSelection) {
			final Object first = ((StructuredSelection) selection).getFirstElement();
			IProject tempProject = null;
			if (first instanceof IAdaptable) {
				Object adapter = ((IAdaptable) first).getAdapter(IProject.class);
				if (adapter != null) {
					tempProject = (IProject) adapter;
				}
			} else if (first instanceof IProject) {
				tempProject = (IProject) first;
			}
			if (tempProject != null) {
				final IProject project = tempProject;
				
				final Thread testThread = new Thread() {
					@Override
					public void run() {
						try {	
							project.build(IncrementalProjectBuilder.FULL_BUILD, new NullProgressMonitor() {
								private int countTasks = 0;
								
								@Override
								public void beginTask(String name, int totalWork) {
									++countTasks;
								}

								@Override
								public void done() {
									if (--countTasks == 0) {
										new ConfigurationBuilder(CorePlugin.getFeatureProject(project), BuildType.ALL_CURRENT, false, "ICPL", 2, BuildOrder.DEFAULT, false);
									}
								}
							});
						} catch (CoreException e) {
							UIPlugin.getDefault().logError(e);
						}
					}
				};
				testThread.start();
				return;
			}
		}
		System.out.println("No valid selection!");
	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		this.selection = selection;
	}

	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

	@Override
	public void init(IWorkbenchWindow window) {
		// TODO Auto-generated method stub

	}

}
