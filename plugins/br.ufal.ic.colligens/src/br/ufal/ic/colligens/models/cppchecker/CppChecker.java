package br.ufal.ic.colligens.models.cppchecker;

/*
 * Author: FLAVIO MEDEIROS
 *
 * Use this class to analyze a specific path with source codes of projects.
 * For each project source code, this class will generate an XML file with
 * the error candidates that CppCheck identifies for each configuration.
 * Set the path in the variable PROJECT_PATH. At the end, you can check
 * all XML files in the results folder.
 *
 */

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;

import br.ufal.ic.colligens.activator.Colligens;

public class CppChecker {

	private String xmlFile = "";

	public CppChecker() {
		xmlFile = "<?xml version=\"1.0\" encoding=\"UTF-8\"?> \n";
		xmlFile += "<results> \n";
	}

	public String getXmlFile() {
		xmlFile += "</results>";
		return xmlFile;
	}

	public void checkProjects(File path, String projectName) {
		for (final File file : path.listFiles()) {
			if (!file.isDirectory()) {
				if (file.getName().endsWith(".c") || file.getName().endsWith(".h")) {
					try {

						final Process proc =
							new ProcessBuilder(Colligens.getDefault().getPreferenceStore().getString("CppCheck"), "--xml", "--force", file.getAbsolutePath())
									.redirectErrorStream(true).start();
						final BufferedReader stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));

						String s = null;
						String config = null;

						// read the output from the command
						while ((s = stdInput.readLine()) != null) {
							s = s.trim();

							if (s.startsWith("Checking")) {
								if (s.contains(":")) {
									final String[] parts = s.split(":");
									if (parts.length > 1) {
										parts[1] = parts[1].trim();
										config = parts[1].replace("...", "");
									}
								} else {
									config = "1";
								}
							}
							if (s.startsWith("<error file") && !s.contains("/" + projectName + "/bin/")) {
								xmlFile += "\t" + s.replace("/>", " config=\"" + config + "\"/>") + "\n";
							}

						}

					} catch (final IOException e) {
						System.out.println("Error analyzing file + " + file.getAbsolutePath() + "...");
						e.printStackTrace();
					}
				}
			} else {
				checkProjects(file, projectName);
			}
		}
	}

	public void checkFile(File file, String projectName) {

		try {

			final Process proc =
				new ProcessBuilder(Colligens.getDefault().getPreferenceStore().getString("CppCheck"), "--xml", "--force", file.getAbsolutePath())
						.redirectErrorStream(true).start();
			final BufferedReader stdInput = new BufferedReader(new InputStreamReader(proc.getInputStream()));

			String s = null;
			String config = null;

			// read the output from the command
			while ((s = stdInput.readLine()) != null) {
				s = s.trim();

				if (s.startsWith("Checking")) {
					if (s.contains(":")) {
						final String[] parts = s.split(":");
						if (parts.length > 1) {
							parts[1] = parts[1].trim();
							config = parts[1].replace("...", "");
						}
					} else {
						config = "1";
					}
				}
				if (s.startsWith("<error file") && !s.contains("/" + projectName + "/bin/")) {
					xmlFile += "\t" + s.replace("/>", " config=\"" + config + "\"/>") + "\n";
				}

			}

		} catch (final IOException e) {
			System.out.println("Error analyzing file + " + file.getAbsolutePath() + "...");
			e.printStackTrace();
		}
	}

}
