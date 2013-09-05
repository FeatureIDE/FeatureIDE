package br.ufal.ic.colligens.controllers;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.ui.IWorkbenchWindow;

import br.ufal.ic.colligens.controllers.metrics.MetricsViewController;
import br.ufal.ic.colligens.util.Statistics;
import br.ufal.ic.colligens.util.metrics.CountDirectives;
import br.ufal.ic.colligens.util.metrics.MetricsException;

public class MetricsController {
	private ProjectExplorerController pkgExplorerController;

	public MetricsController() {
		pkgExplorerController = new ProjectExplorerController();
	}

	public void setWindow(IWorkbenchWindow window) {
		pkgExplorerController.setWindow(window);
	}

	/**
	 * @throws MetricsException
	 */
	public void run() throws MetricsException {
		try {
			pkgExplorerController.run();

			List<String> listFiles = pkgExplorerController.getListToString();

			if (listFiles.isEmpty()) {
				throw new ProjectExplorerException("Not a valid file found C");
			}

			int numberFiles = 0;
			int numberFilesWithDirec = 0;
			int directivesPerFile = 0;
			int LOC = 0;

			CountDirectives countDirectives = new CountDirectives();

			for (Iterator<String> iterator = listFiles.iterator(); iterator
					.hasNext();) {
				String file = (String) iterator.next();
				numberFiles++;
				try {
					CountDirectives countDirective = new CountDirectives();
					int count = countDirective.count(file);
					LOC = LOC + countDirective.numberLine;
					if (count > 0) {
						numberFilesWithDirec++;
						if (directivesPerFile == 0) {
							directivesPerFile = count;
						} else {
							directivesPerFile = (directivesPerFile + count) / 2;
						}
						countDirectives.directives
								.addAll(countDirective.directives);
					}
				} catch (Exception e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
					throw new MetricsException("unexpected error!");
				}
			}

			LinkedList<Statistics> list = new LinkedList<Statistics>();

			Statistics statistics = new Statistics("Number of directives", ""
					+ countDirectives.directives.size());
			list.add(statistics);

			// statistics = new Statistics("Number of products", "32");
			// list.add(statistics);

			statistics = new Statistics("Number of files", "" + numberFiles);
			list.add(statistics);

			statistics = new Statistics("Number of files with directives", ""
					+ numberFilesWithDirec);
			list.add(statistics);

			statistics = new Statistics("Directives per file (median)", ""
					+ (directivesPerFile));
			list.add(statistics);

			statistics = new Statistics("LOC", "" + LOC);
			list.add(statistics);

			MetricsViewController statisticsViewController = MetricsViewController
					.getInstance();

			statisticsViewController.setInput(list);
			
		} catch (ProjectExplorerException e) {
			return;
		}
	}
}
