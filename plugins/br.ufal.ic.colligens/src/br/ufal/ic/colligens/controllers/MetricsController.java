package br.ufal.ic.colligens.controllers;

import static de.ovgu.featureide.fm.core.localization.StringTable.LOC;
import static de.ovgu.featureide.fm.core.localization.StringTable.NOT_A_VALID_FILE_FOUND_C;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_DIRECTIVES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_FILES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF_FILES_WITH_DIRECTIVES;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IWorkbenchWindow;

import br.ufal.ic.colligens.controllers.metrics.MetricsViewController;
import br.ufal.ic.colligens.util.metrics.CountDirectives;
import br.ufal.ic.colligens.util.metrics.Metrics;
import br.ufal.ic.colligens.util.metrics.MetricsException;

public class MetricsController {

	private final ProjectExplorerController pkgExplorerController;

	public MetricsController() {
		pkgExplorerController = new ProjectExplorerController();
	}

	public void setWindow(IWorkbenchWindow window) {
		pkgExplorerController.setWindow(window);
	}

	public void setSelection(ISelection selection) {
		pkgExplorerController.setSelection(selection);
	}

	/**
	 * @throws MetricsException
	 */
	public void run() {

		try {
			pkgExplorerController.run();

			final List<String> listFiles = pkgExplorerController.getListToString();

			if (listFiles.isEmpty()) {
				throw new ProjectExplorerException(NOT_A_VALID_FILE_FOUND_C);
			}

			int numberFiles = 0;
			int numberFilesWithDirec = 0;
			int directivesPerFile = 0;
			int LinesOfCode = 0;

			final CountDirectives countDirectives = new CountDirectives();

			for (final Iterator<String> iterator = listFiles.iterator(); iterator.hasNext();) {
				final String file = iterator.next();
				numberFiles++;
				try {
					final CountDirectives countDirective = new CountDirectives();
					final int count = countDirective.count(file);
					LinesOfCode = LinesOfCode + countDirective.numberLine;
					if (count > 0) {
						numberFilesWithDirec++;
						if (directivesPerFile == 0) {
							directivesPerFile = count;
						} else {
							directivesPerFile = (directivesPerFile + count) / 2;
						}
						countDirectives.directives.addAll(countDirective.directives);
					}
				} catch (final Exception e) {

				}
			}

			final LinkedList<Metrics> list = new LinkedList<Metrics>();

			Metrics statistics = new Metrics(NUMBER_OF_DIRECTIVES, "" + countDirectives.directives.size());
			list.add(statistics);

			// statistics = new Statistics(NUMBER_OF_PRODUCTS, "32");
			// list.add(statistics);

			statistics = new Metrics(NUMBER_OF_FILES, "" + numberFiles);
			list.add(statistics);

			statistics = new Metrics(NUMBER_OF_FILES_WITH_DIRECTIVES, "" + numberFilesWithDirec);
			list.add(statistics);

			statistics = new Metrics("Directives per file (median)", "" + (directivesPerFile));
			list.add(statistics);

			statistics = new Metrics(LOC, "" + LOC);
			list.add(statistics);

			final MetricsViewController statisticsViewController = MetricsViewController.getInstance();

			statisticsViewController.setInput(list);

		} catch (final ProjectExplorerException e) {

		}

	}
}
