package de.ovgu.featureide.visualisation;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.Platform;
import org.eclipse.swt.SWT;
import org.eclipse.swt.SWTError;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.osgi.framework.Bundle;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
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
		}
		boolean[][] matrix = null;
		IFeatureProject featureProject = CorePlugin.getFeatureProject(project);
		try {
			matrix = getConfigsMatrix(featureProject);
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
		List<String> featureList = (List<String>) featureProject.getFeatureModel().getFeatureOrderList();
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

		File f = getFileFromPlugin("de.ovgu.featureide.visualisation","template/cooccurrence/page.html");
		String html = getStringOfFile(f);
		html = html.replaceFirst("JSON_CONTENT", json.toString());
		
		browser.setText(html);
		shell.open();
	}

	private int getCoocurrence(boolean[][] matrix, int i, int i2) {
		int occurrences = 0;
		for (int o = 0; o < matrix.length; o++) {
			if (matrix[o][i] && matrix[o][i2]) {
				occurrences++;
			}
		}
		return occurrences;
	}

	boolean[][] getConfigsMatrix(IFeatureProject featureProject) throws CoreException {

		Collection<String> featureList = featureProject.getFeatureModel().getFeatureOrderList();
		Collection<IFile> configs = new ArrayList<IFile>();

		IFolder configsFolder = featureProject.getConfigFolder();
		for (IResource res : configsFolder.members()) {
			if (res instanceof IFile) {
				if (((IFile) res).getName().endsWith(".config")) {
					configs.add((IFile) res);
				}
			}
		}

		boolean[][] matrix = new boolean[configs.size()][featureList.size()];

		int iconf = 0;
		for (IFile config : configs) {
			final Configuration configuration = new Configuration(featureProject.getFeatureModel());
			FileHandler.load(Paths.get(config.getLocationURI()), configuration, ConfigurationManager.getFormat(config.getName()));
			Set<String> configFeatures = configuration.getSelectedFeatureNames();
			int ifeat = 0;
			for (String f : featureList) {
				matrix[iconf][ifeat] = configFeatures.contains(f);
				ifeat++;
			}
			iconf++;
		}

		return matrix;
	}
	
	
	public File getFileFromPlugin(String pluginId, String relativePath){
		Bundle bundle = Platform.getBundle(pluginId);
		URL fileURL = bundle.getEntry(relativePath);
		File file = null;
		try {
		    file = new File(FileLocator.resolve(fileURL).toURI());
		} catch (URISyntaxException e1) {
		    e1.printStackTrace();
		} catch (IOException e1) {
		    e1.printStackTrace();
		}
		return file;
	}
	
	public static List<String> getLinesOfFile(File file) {
		List<String> lines = new ArrayList<String>();
		try {
			FileInputStream fstream = new FileInputStream(file);
			DataInputStream in = new DataInputStream(fstream);
			BufferedReader br = new BufferedReader(new InputStreamReader(in));
			String strLine;
			while ((strLine = br.readLine()) != null) {
				lines.add(strLine);
			}
			in.close();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return lines;
	}

	public static String getStringOfFile(File file) {
		StringBuilder string = new StringBuilder();
		for (String line : getLinesOfFile(file)) {
			string.append(line + "\n");
		}
		string.setLength(string.length() - 1);
		return string.toString();
	}
	

}
