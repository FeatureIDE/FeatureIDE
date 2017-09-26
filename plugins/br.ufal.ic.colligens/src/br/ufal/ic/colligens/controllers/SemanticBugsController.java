package br.ufal.ic.colligens.controllers;

import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbenchWindow;

import br.ufal.ic.colligens.controllers.semanticbugs.SemanticBugsViewController;
import br.ufal.ic.colligens.models.cppchecker.CppCheckAnalyzer;
import br.ufal.ic.colligens.models.cppchecker.CppCheckerFileLogs;
import br.ufal.ic.colligens.util.metrics.MetricsException;

public class SemanticBugsController {

	private final ProjectExplorerController projectExplorer;

	public SemanticBugsController() {
		projectExplorer = new ProjectExplorerController();
	}

	public void setWindow(IWorkbenchWindow window) {
		projectExplorer.setWindow(window);
	}

	public void setSelection(ISelection selection) {
		projectExplorer.setSelection(selection);
	}

	/**
	 * @throws MetricsException
	 */
	public void run() {
		try {

			projectExplorer.run();

			final List<IResource> resources = projectExplorer.getList();

			Display.getDefault().asyncExec(new Runnable() {

				@Override
				public void run() {
					final CppCheckAnalyzer analyser = new CppCheckAnalyzer();

					for (final Iterator<IResource> iterator = resources.iterator(); iterator.hasNext();) {

						final IResource iResource = iterator.next();

						// System.out.println(iResource);

						analyser.processFile((IFile) iResource);

					}

					final List<CppCheckerFileLogs> fileLogs = analyser.getFiles();

					// returns the list to view
					final SemanticBugsViewController statisticsViewController = SemanticBugsViewController.getInstance();

					statisticsViewController.setInput(fileLogs);

				}

			});

		} catch (final ProjectExplorerException e1) {

		}
	}
}
