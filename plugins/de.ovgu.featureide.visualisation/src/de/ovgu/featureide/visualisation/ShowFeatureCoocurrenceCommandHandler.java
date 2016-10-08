package de.ovgu.featureide.visualisation;

import java.io.File;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.swt.SWT;
import org.eclipse.swt.SWTError;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.ui.handlers.base.ASelectionHandler;

/**
 * Show Feature Co-occurrence
 * 
 * @author jabier.martinez
 */
public class ShowFeatureCoocurrenceCommandHandler extends ASelectionHandler {

	@Override
	protected void singleAction(Object element) {
		IProject project = null;
		if (!(element instanceof IProject)) {
			if (element instanceof IAdaptable) {
				project = ((IAdaptable) element).getAdapter(IProject.class);
			}
		} else {
			project = (IProject)element;
		}
		boolean[][] matrix = null;
		IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		List<String> featureList = ConfigAnalysisUtils.getNoCoreNoHiddenFeatures(featureProject);
		try {
			matrix = ConfigAnalysisUtils.getConfigsMatrix(featureProject, featureList);
		} catch (CoreException e) {
			e.printStackTrace();
		}

		Shell shell = new Shell(Display.getCurrent());
		shell.setLayout(new FillLayout());
		shell.setMaximized(true);
		Browser browser;
		try {
			browser = new Browser(shell, SWT.NONE);
		} catch (SWTError e) {
			System.out.println("Could not instantiate Browser: " + e.getMessage());
			return;
		}

		StringBuffer json = new StringBuffer("{\"nodes\":[");
		for (String f : featureList) {
			json.append("{\"name\":\"");
			json.append(f);
			json.append("\",\"group\":2},");
		}
		json.setLength(json.length() - 1); // remove last comma
		json.append("],\"links\":[");

		boolean atleastone = false;
		for (int i = 0; i < featureList.size(); i++) {
			for (int i2 = i + 1; i2 < featureList.size(); i2++) {
				int value = getCoocurrence(matrix, i, i2);
				if (value > 0) {
					atleastone = true;
					json.append("{\"source\":");
					json.append(i);
					json.append(",\"target\":");
					json.append(i2);
					json.append(",\"value\":");
					json.append(value);
					json.append("},");
				}
			}
		}
		if (!atleastone) {
			json.setLength(json.length() - "],\"links\":[".length());
		} else {
			json.setLength(json.length() - 1); // remove last comma
		}

		json.append("]}");

		File f = Utils.getFileFromPlugin("de.ovgu.featureide.visualisation", "template/cooccurrence/page.html");
		String html = Utils.getStringOfFile(f);
		html = html.replaceFirst("// DATA_HERE", " myjson ='" + json.toString() + "';");

		browser.setText(html);
		shell.open();
	}

	public static int getCoocurrence(boolean[][] matrix, int i, int i2) {
		int occurrences = 0;
		for (int o = 0; o < matrix.length; o++) {
			if (matrix[o][i] && matrix[o][i2]) {
				occurrences++;
			}
		}
		return occurrences;
	}

}
