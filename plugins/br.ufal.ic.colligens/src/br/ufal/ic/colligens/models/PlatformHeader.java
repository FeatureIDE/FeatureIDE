package br.ufal.ic.colligens.models;

import static de.ovgu.featureide.fm.core.localization.StringTable.GENERATING_PLATFORM;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Pattern;

import org.eclipse.cdt.core.model.CModelException;
import org.eclipse.cdt.core.model.IIncludeReference;

import br.ufal.ic.colligens.activator.Colligens;

public class PlatformHeader extends AbstractHeader {

	@Override
	public void run() throws PlatformException {
		new File(Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "projects").mkdirs();

		File platform;

		platform = new File(getIncludePath());

		if (platform.exists()) {
			return;
		}

		List<String> listFiles;

		listFiles = filesAllProject();

		monitorbeginTask(GENERATING_PLATFORM, listFiles.size());

		IIncludeReference includes[] = null;
		try {
			includes = super.getProject().getIncludeReferences();
		} catch (final CModelException e) {

			e.printStackTrace();
		}

		List<String> arglist;
		final Collection<String> platformTemp = new HashSet<String>();

		for (final Iterator<String> iterator = listFiles.iterator(); iterator.hasNext();) {
			final String filePath = iterator.next();
			System.out.println(filePath);
			super.monitorWorked(1);
			super.monitorSubTask(filePath);
			if (monitorIsCanceled()) {
				return;
			}
			// System.out.println(filePath);

			arglist = new ArrayList<String>();
			arglist.add(Colligens.getDefault().getPreferenceStore().getString("GCC"));
			arglist.add("-dM");
			arglist.add("-E");
			arglist.add("-std=gnu99");

			if (!Colligens.getDefault().getPreferenceStore().getString("LIBS").contentEquals("")) {
				arglist.add(Colligens.getDefault().getPreferenceStore().getString("LIBS"));
			}

			for (int i = 0; i < includes.length; i++) {
				arglist.add("-I" + includes[i].getElementName());
			}

			arglist.add(filePath);

			final ProcessBuilder processBuilder = new ProcessBuilder(arglist);

			BufferedReader input = null;
			BufferedReader error = null;
			try {
				final Process process = processBuilder.start();
				input = new BufferedReader(new InputStreamReader(process.getInputStream(), Charset.availableCharsets().get("UTF-8")));
				error = new BufferedReader(new InputStreamReader(process.getErrorStream(), Charset.availableCharsets().get("UTF-8")));
				boolean execute = true;

				while (execute) {

					try {
						String line;
						String errorLine = "";
						try {

							while ((line = input.readLine()) != null) {
								line = line.trim();
								if (!platformTemp.contains(line)) {
									if (line.contains("#define ")) {
										final String[] temp = line.trim().split(Pattern.quote(" "));
										if (super.countDirectives.directives.contains(temp[1])) {
											continue;
										} else if (line.endsWith("_H_") || line.endsWith("_H")) {
											// line = "#undef " + temp[1];
											if (platformTemp.contains(line)) {
												continue;
											}
										}
									}
									// System.err.println(line);
									platformTemp.add(line);
								}
							}
							errorLine = "";
							while ((line = error.readLine()) != null) {
								// if (line.contains(FATAL_ERROR)) {
								errorLine = errorLine + line + "\n";
								// break;
								// }
								System.err.println(line);
							}
						} catch (final Exception e) {
							e.printStackTrace();
							Colligens.getDefault().logError(e);
						}

						try {
							process.waitFor();
						} catch (final InterruptedException e) {
							System.out.println(e.toString());
							Colligens.getDefault().logError(e);
						}
						final int exitValue = process.exitValue();
						if (exitValue != 0) {
							platform.deleteOnExit();

							if (errorLine.equals("")) {
								errorLine = "Was not possible to locate all the includes (exit=" + exitValue + ")!";
							}
							throw new PlatformException(errorLine);
						}

						execute = false;
					} catch (final IllegalThreadStateException e) {
						System.out.println(e.toString());
						Colligens.getDefault().logError(e);
					}
				}

			} catch (final IOException e) {
				System.out.println(e.toString());
				Colligens.getDefault().logError(e);
			} finally {
				try {
					if (input != null) {
						input.close();
					}

				} catch (final IOException e) {
					Colligens.getDefault().logError(e);
				} finally {
					if (error != null) {
						try {
							error.close();
						} catch (final IOException e) {
							Colligens.getDefault().logError(e);
						}
					}
				}
			}
		}

		FileWriter fileW;
		try {
			fileW = new FileWriter(platform);
			final BufferedWriter buffW = new BufferedWriter(fileW);

			for (final String line : platformTemp) {

				buffW.write(line + "\n");
			}
			buffW.close();
			fileW.close();
		} catch (final IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

	@Override
	public String getIncludePath() {
		// return super.getProject().getProject().getLocation().toOSString()
		// + "/platform.h";

		return Colligens.getDefault().getConfigDir().getAbsolutePath() + System.getProperty("file.separator") + "projects"
			+ System.getProperty("file.separator") + super.getProject().getProject().getProject().getName() + "_platform.h";

	}

	@Override
	public Collection<String> getIncludes() {
		final ArrayList<String> collection = new ArrayList<String>();

		collection.add(getIncludePath());

		return collection;
	}

}
