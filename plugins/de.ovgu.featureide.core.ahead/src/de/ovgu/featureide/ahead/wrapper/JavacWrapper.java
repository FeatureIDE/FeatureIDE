/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ahead.wrapper;

import static de.ovgu.featureide.ahead.wrapper.AheadBuildErrorType.JAVAC_ERROR;

import java.io.CharArrayWriter;
import java.io.PrintWriter;
import java.util.LinkedList;
import java.util.Scanner;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import com.sun.tools.javac.Main;

import de.ovgu.featureide.ahead.AheadCorePlugin;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;


/**
 * The class encapsulates everything that has to do with the
 * compile step. It uses the javac package from the tools.jar
 * to compile java files to class files. Its main task is to
 * parse the error messages provided by the java compiler and
 * to dispatch an event when a syntax error occurs.
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 *
 */
public class JavacWrapper {

	private IFeatureProject featureProject;

	private LinkedList<AheadBuildErrorListener> errorListeners;

	private final static Pattern errorMessagePattern = Pattern
			.compile("(.+):(\\d+):(.+)");

	public JavacWrapper(IFeatureProject featureProject) {
		this.featureProject = featureProject;
		errorListeners = new LinkedList<AheadBuildErrorListener>();
	}

	public void addBuildErrorListener(AheadBuildErrorListener listener) {
		if (!errorListeners.contains(listener))
			errorListeners.add(listener);
	}

	public void removeBuildErrorListener(AheadBuildErrorListener listener) {
		errorListeners.remove(listener);
	}

	@SuppressWarnings("deprecation")
	public void compile(IFile[] files) {
		String sep = System.getProperty("path.separator");
		String classpath = "";
		for (String path : featureProject.getJavaClassPath())
			classpath += sep + path;
		classpath = classpath.substring(1);
		IFolder folder = featureProject.getBinFolder();
		try {
			if (!folder.exists())
				folder.create(false, true, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		String[] options = new String[4 + files.length];
		int pos = 0;
		options[pos++] = "-d";
		options[pos++] = featureProject.getBinFolder().getRawLocation().toOSString();
		options[pos++] = "-classpath";
		options[pos++] = classpath;
		for (IFile file : files)
			options[pos++] = file.getRawLocation().toOSString();

		CharArrayWriter charWriter = new CharArrayWriter();
		PrintWriter pwriter = new PrintWriter(charWriter);
		Main.compile(options, pwriter);
		
		parseJavacOutput(charWriter.toString(), files);

		IFolder outputFolder = featureProject.getBinFolder().getFolder(files[0].getParent().getName());
		for (IFile javaFile : files) {
			String fileName = javaFile.getName();
			fileName = fileName.substring(0, fileName.lastIndexOf('.')) + ".class";
			IFile classFile = outputFolder.getFile(fileName);
			try {
				classFile.refreshLocal(IResource.DEPTH_ZERO, null);
				if (classFile.exists())
					classFile.setDerived(true);
			} catch (CoreException e) {
				AheadCorePlugin.getDefault().logError(e);
			}
		}
	}

	public void parseJavacOutput(String output, IFile[] sources) {
		if (output.length() == 0)
			return;

		TreeMap<String, IFile> sourcePaths = new TreeMap<String, IFile>();
		for (IFile file : sources)
			sourcePaths.put(file.getRawLocation().toOSString(), file);

		Scanner scanner = new Scanner(output);
		String currentLine;
		while (scanner.hasNextLine()) {
			currentLine = scanner.nextLine();

			Matcher matcher = errorMessagePattern.matcher(currentLine);
			if (!matcher.find() || !sourcePaths.containsKey(matcher.group(1)))
				continue;
			IFile currentFile = sourcePaths.get(matcher.group(1));
			int line = Integer.parseInt(matcher.group(2));

			String errorMessage = matcher.group(3);
			errorMessage = errorMessage.substring(1);

			if (errorMessage.equals("cannot find symbol")) {
				errorMessage = parseCannotFindSymbolMessage(scanner);
			}
			AheadBuildErrorEvent evt = new AheadBuildErrorEvent(currentFile, errorMessage, JAVAC_ERROR, line);
			for (AheadBuildErrorListener listener : errorListeners)
				listener.parseErrorFound(evt);
		}
	}

	private String parseCannotFindSymbolMessage(Scanner scanner) {
		while (scanner.hasNextLine()) {
			String currentLine = scanner.nextLine();
			if (currentLine.startsWith("symbol")) {
				String[] tokens = currentLine.split(": ");
				if (tokens.length == 2)
					return "Cannot find symbol: "+ tokens[1].substring(0);
				break;
			}
		}
		return "Cannot find symbol";
	}

}
