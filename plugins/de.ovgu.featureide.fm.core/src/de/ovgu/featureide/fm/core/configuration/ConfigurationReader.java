/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.StringTokenizer;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;

/**
 * Reads a configuration from file or String.
 */
public class ConfigurationReader {

	private Configuration configuration;

	private LinkedList<String> warnings = new LinkedList<String>();
	private LinkedList<Integer> positions = new LinkedList<Integer>();

	public ConfigurationReader(Configuration configuration) {
		this.configuration = configuration;
	}

	public boolean readFromFile(IFile file) throws CoreException, IOException {
		String fileName = file.getRawLocation().toOSString();
		InputStream inputStream = new FileInputStream(fileName);
		try {
			return readFromInputStream(inputStream);
		} finally {
			inputStream.close();
		}
	}

	public boolean readFromString(String text) {
		InputStream inputStream = null;
		try {
			inputStream = new ByteArrayInputStream(text.getBytes(Charset
					.availableCharsets().get("UTF-8")));
			return readFromInputStream(inputStream);
		} catch (IOException e) {
			FMCorePlugin.getDefault().logError(e);
		} finally {
			if (inputStream != null) {
				try {
					inputStream.close();
				} catch (IOException e) {
					FMCorePlugin.getDefault().logError(e);
				}
			}
		}
		return false;
	}

	private boolean readFromInputStream(InputStream inputStream)
			throws IOException {
		configuration.resetValues();
		BufferedReader reader = null;
		String line = null;
		Integer lineNumber = 1;
		boolean successful = true;
		try {
			reader = new BufferedReader(new InputStreamReader(inputStream,
					Charset.availableCharsets().get("UTF-8")));
			while ((line = reader.readLine()) != null) {
				if (line.startsWith("#") || line.isEmpty() || line.equals(" ")) {
					lineNumber++;
					continue;
				}
				// the string tokenizer is used to also support the expression
				// format used by FeatureHouse
				StringTokenizer tokenizer = new StringTokenizer(line);
				LinkedList<String> hiddenFeatures = new LinkedList<String>();
				while (tokenizer.hasMoreTokens()) {
					String name = tokenizer.nextToken(" ");
					if (name.startsWith("\"")) {
						try {
							name = name.substring(1);
							name += tokenizer.nextToken("\"");
						} catch (NoSuchElementException e) {
							successful = false;
							warnings.add("Feature '"
									+ name
									+ "' is corrupt. No ending quotation marks found.");
							positions.add(lineNumber);
							return false;
						} catch (NullPointerException e) {
							successful = false;
							warnings.add("Feature '"
									+ name
									+ "' is corrupt. No ending quotation marks found.");
							positions.add(lineNumber);
							return false;
						}
						// Check for ending quotation mark
						try {
							String endingDelimiter = tokenizer.nextToken(" ");
							if (!endingDelimiter.startsWith("\"")) {
								successful = false;
								warnings.add("Feature '"
										+ name
										+ "' is corrupt. No ending quotation marks found.");
								positions.add(lineNumber);
								return false;
							}
						} catch (Exception e) {
							successful = false;
							warnings.add("Feature '"
									+ name
									+ "' is corrupt. No ending quotation marks found.");
							positions.add(lineNumber);
							return false;
						}
					}

					Feature feature = configuration.getFeatureModel()
							.getFeature(name);
					if (feature != null && feature.hasHiddenParent()) {
						hiddenFeatures.add(name);
					} else {
						try {
							configuration.setManual(name, Selection.SELECTED);
						} catch (FeatureNotFoundException e) {
							successful = false;
							warnings.add("Feature " + name + " does not exist");
							positions.add(lineNumber);
							return false;
						} catch (SelectionNotPossibleException e) {
							successful = false;
							warnings.add("Feature " + name
									+ " cannot be selected");
							positions.add(lineNumber);
							return false;
						}
					}
				}
				for (String name : hiddenFeatures) {
					try {
						configuration.setAutomatic(name, Selection.SELECTED);
					} catch (FeatureNotFoundException e) {
						successful = false;
						warnings.add("Feature " + name + " does not exist");
						positions.add(lineNumber);
						return false;
					} catch (SelectionNotPossibleException e) {
						successful = false;
						warnings.add("Feature " + name + " cannot be selected");
						positions.add(lineNumber);
						return false;
					}
				}
				lineNumber++;
			}
		} finally {
			if (reader != null) {
				reader.close();
			}
		}
		return successful;
	}

	public List<String> getWarnings() {
		return Collections.unmodifiableList(warnings);
	}

	public List<Integer> getPositions() {
		return Collections.unmodifiableList(positions);
	}

}
