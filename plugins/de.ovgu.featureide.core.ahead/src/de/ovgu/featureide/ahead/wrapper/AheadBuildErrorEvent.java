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

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.ahead.AheadCorePlugin;

import featureide.fm.core.io.PosString;

/**
 * The AheadBuildErrorEvent is dispatched when ever a syntax error was found
 * during the compilation step. The Event contains all needed information to
 * set an error marker
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 *
 */
public class AheadBuildErrorEvent {
	
	private IResource file;
	
	private String message;
	
	private AheadBuildErrorType type;
	
	private int line;
	
	public AheadBuildErrorEvent(IResource source, String message, AheadBuildErrorType type, int line) {
		this.type = type;
		this.file = source;
		this.line = line;
		if (type == AheadBuildErrorType.COMPOSER_ERROR) {
			this.message = "Composer: " + message;
			//nothing else to do, because its already the position at the source jak file
		}
		else if (type == AheadBuildErrorType.JAVAC_ERROR) {
			this.message = "Javac: " + message;
			initJavacErrorEvent();
		}
		else
			throw new RuntimeException("Unknown AheadBuildErrorType \"" + type + "\"!");
	}
	
	private void initJavacErrorEvent() {
		try {
			convertToComposedJak();
			calculateJakLine();
		} catch (Exception e) {
			//if calculation failes the error will be at the old position
			e.printStackTrace();
		}
	}

	//private static Pattern inheritedPattern = Pattern.compile("(// inherited constructors(?:[^{}]+|\\{[^{}]+\\})+\\{[^{}]+\\})\\s*}");
	private static Pattern inheritedPattern = Pattern.compile("(// inherited constructors(?:[^{}]+|\\{[^{}]+\\})+)\\}");
	
	private void convertToComposedJak() throws CoreException, IOException {
		IFile javaFile = (IFile) this.file;
		int javaLine = this.line;
		
		String javaName = javaFile.getName();
		String jakName = javaName.substring(0, javaName.lastIndexOf('.')) + ".jak"; 
		IFile composedJakFile = ((IFolder) javaFile.getParent()).getFile(jakName);

		int composedJakLine = javaLine;
		javaFile.refreshLocal(IResource.DEPTH_ZERO, null);
		String contentString = getString(javaFile);
		PosString content = new PosString(contentString);
		Matcher matcher = inheritedPattern.matcher(content.string);
		while (matcher.find()) {
			content.pos = matcher.end(1);
			if (content.lineNumber() >= javaLine)
				break;
			composedJakLine -= new PosString(matcher.group(1), matcher.end(1)).lineNumber();
		}
		
		this.file = composedJakFile;
		this.line = composedJakLine;
	}

	private static Pattern jakPattern = Pattern.compile("SoUrCe[^\"]+\"([^\"]+)\";");
	
	private void calculateJakLine() throws CoreException, IOException {
		AheadCorePlugin.getDefault().logInfo("Calculate jak source line for file " + file);
		IFile composedJakFile = (IFile) this.file;
		int composedJakLine = this.line;
		
		composedJakFile.refreshLocal(IResource.DEPTH_ZERO, null);
		String contentString = getString(composedJakFile);
		PosString content = new PosString(contentString);
		Matcher matcher = jakPattern.matcher(content.string);
		String filename = null;
		int line = 0;
		while (matcher.find(content.pos)) {
			content.pos = matcher.end(1);
			int newLine = content.lineNumber();
			if (newLine >= composedJakLine)
				break;
			line = newLine;
			filename = matcher.group(1);
			AheadCorePlugin.getDefault().logInfo(filename);
		}
		
		if (filename == null) {
			lookupImportInAllJakFiles(contentString, matcher);
		}
		else {
			IFile jakFile = getJakFile(filename);
			AheadCorePlugin.getDefault().logInfo(jakFile.getFullPath().toOSString());
			int jakLine = composedJakLine - line + 1;
			jakLine += numberOfImportLines(jakFile);
			jakLine += lineNumberOfLayerDeclaration(jakFile);
			
			this.file = jakFile;
			this.line = jakLine;
		}
	}

	private void lookupImportInAllJakFiles(String composedJakContent, Matcher matcher) throws CoreException, IOException {
		AheadCorePlugin.getDefault().logInfo("Looking for source of error on import for file " + file);
		int a = 0;
		int b = 0;
		for (int i = 0; i < line; i++) {
			if (b < 0)
				return;
			a = b;
			b = composedJakContent.indexOf('\n', b) + 1;
		}
		b = b < 0 ? composedJakContent.length() : b;
		String importString = composedJakContent.substring(a, b).trim();
		
		do {
			IFile jakFile = getJakFile(matcher.group(1));
			if (jakFile != null) {
				String text = getString(jakFile);
				int pos = text.indexOf(importString);
				if (pos >= 0) {
					this.line = new PosString(text, pos).lineNumber();
					this.file = jakFile;
					return;
				}
			}
		}
		while (matcher.find());
	}

	private IFile getJakFile(String filename) {
		String relativeFilename = filename;
		IProject project = file.getProject();
		relativeFilename = relativeFilename.substring(relativeFilename
				.indexOf(project.getName())
				+ project.getName().length() + 1);
		IFile newFile = project.getFile(relativeFilename);
		if (newFile.exists())
			return newFile;
		
		AheadCorePlugin.getDefault().logWarning("Was not able to locate an error in the source jak file '" + filename + "'");
		return null;
		
//		//check if the file name is relative
//		newFile = project.getFile("../" + filename);
//		AheadCorePlugin.getDefault().logInfo(newFile.getFullPath().toOSString());
//		if (newFile.exists())
//			return newFile;
//
//		//otherwise it is absolute
//		int pathLength = project.getLocation().toOSString().length();
//		AheadCorePlugin.getDefault().logInfo(project.getLocation().toOSString());
//		while (filename.startsWith("../")) {
//			filename = filename.substring(3);
//		}
//		AheadCorePlugin.getDefault().logInfo(filename);
//		//remove project path from filename (except 3 characters like "c:\")
//		//TODO #27: jak file error propagation for unix
//		filename = filename.substring(pathLength - 3);
//		AheadCorePlugin.getDefault().logInfo(filename);
//		newFile = project.getFile(filename);
//		if (newFile.exists())
//			return newFile;
	}

	private static Pattern importPattern = Pattern.compile("(import)\\s[^;\\(\\)\\{\\}\\[\\]]+;");

	private int numberOfImportLines(IFile jakFile) throws CoreException, IOException {
		jakFile.refreshLocal(IResource.DEPTH_ZERO, null);
		String contentString = getString(jakFile);
		PosString content = new PosString(contentString);

		Matcher matcher = importPattern.matcher(content.string);
		while (matcher.find(content.pos)) {
			content.pos = matcher.end(1);
		}
		if (content.pos <= 0)
			return 0;
		
		return content.lineNumber() - 1;
	}

	private int lineNumberOfLayerDeclaration(IFile jakFile) throws CoreException, IOException {
		jakFile.refreshLocal(IResource.DEPTH_ZERO, null);
		String contentString = getString(jakFile);
		PosString content = new PosString(contentString);
		content.pos = contentString.indexOf("layer");
		return content.lineNumber() - 1;
	}

	public int getLine() {
		return line;
	}
	
	public String getMessage() {
		return message;
	}
	
	public AheadBuildErrorType getType() {
		return type;
	}
	
	public IResource getResource() {
		return file;
	}
	
    /**
     * Returns a string containing the contents of the given file.
     * 
     * @throws CoreException 
     * @throws IOException 
     */
    public static String getString(IFile file) throws CoreException, IOException {
        InputStream contentStream = file.getContents();
        Reader in = new InputStreamReader(contentStream);

        int chunkSize = contentStream.available();
        StringBuffer buffer = new StringBuffer(chunkSize);
        char[] readBuffer = new char[chunkSize];
        
        int n = in.read(readBuffer);
        while (n > 0) {
            buffer.append(readBuffer);
            n = in.read(readBuffer);
        }

        contentStream.close();
        return buffer.toString();
    }

}
