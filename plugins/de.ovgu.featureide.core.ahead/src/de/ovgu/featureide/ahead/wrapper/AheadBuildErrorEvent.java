/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
import java.nio.charset.Charset;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.ahead.AheadCorePlugin;


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

	public String fileName;

	private Matcher matcher;
	
	/**
	 * Constructor for test purpose<br>
	 * Does nothing.
	 */
	public AheadBuildErrorEvent() {
		
	}
	
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
			if (file.exists()) {
				calculateJakLine();
			}
		} catch (Exception e) {
			//if calculation fails the error will be at the old position
			AheadCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * @throws CoreException
	 * @throws IOException
	 */
	private void convertToComposedJak() throws CoreException, IOException {
		IFile javaFile = (IFile) this.file;
		int javaLine = this.line;
		
		String javaName = javaFile.getName();
		String jakName = javaName.substring(0, javaName.lastIndexOf('.')) + ".jak"; 
		IFile composedJakFile = ((IFolder) javaFile.getParent()).getFile(jakName);

		javaFile.refreshLocal(IResource.DEPTH_ZERO, null);

		this.file = composedJakFile;
		this.line = calculateComposedJakLine(javaLine, getString(javaFile));
	}

	/*
	 * TODO #457 fix wrong line calculation for AHEAD
	 * 
	 * The first pattern causes an endless loop.
	 * 
	 * The second pattern caused a wrong line calculation.
	 * see: Tests @ TAheadErrorPropagation
	 */	
//	private static Pattern inheritedPattern = Pattern.compile("(// inherited constructors(?:[^{}]+|\\{[^{}]+\\})+\\{[^{}]+\\})\\s*}");
	private static Pattern inheritedPattern = Pattern.compile("(// inherited constructors(?:[^{}]+|\\{[^{}]+\\})+)\\}");
	
	/**
	 * Calculates the corresponding line of the composed jak file to the java file
	 *
	 * @param javaLine The line at the java file
	 * @return the line at the composed jak file
	 */
	public int calculateComposedJakLine(int javaLine, String contentString) {
		int composedJakLine = javaLine;
		PosString content = new PosString(contentString);
		Matcher matcher = inheritedPattern.matcher(content.string);
		while (matcher.find()) {
			content.pos = matcher.end(1);
			if (content.lineNumber() >= javaLine)
				break;
			composedJakLine -= new PosString(matcher.group(1), matcher.end(1)).lineNumber();
		}
		return composedJakLine;
	}

	private static Pattern jakPattern = Pattern.compile("SoUrCe[^\"]+\"([^\"]+)\";");
	
	/**
	 * Calculates the line at the jak source files and searches the right feature
	 * @throws CoreException
	 * @throws IOException
	 */
	private void calculateJakLine() throws CoreException, IOException {
		IFile composedJakFile = (IFile) this.file;
		int composedJakLine = this.line;
		
		composedJakFile.refreshLocal(IResource.DEPTH_ZERO, null);
		
		String contentString = getString(composedJakFile);
		int line = setSourceFile(contentString, composedJakLine);
		
		if (fileName == null) {
			this.line = lookupImportInAllJakFiles(contentString, matcher);
		}
		else {
			IFile jakFile = getJakFile(fileName);
			if (jakFile != null) {
				jakFile.refreshLocal(IResource.DEPTH_ZERO, null);
				String jakContent = getString(jakFile);
					
				this.file = jakFile;
				this.line = setSourceLine(composedJakLine, line, jakContent);
			}
		}
	}

	/**
	 * TODO description / rename
	 * @param contentString
	 * @param composedJakLine 
	 * @return
	 */
	public int setSourceFile(String contentString, int composedJakLine) {
		PosString content = new PosString(contentString);
		matcher = jakPattern.matcher(content.string);
		int line = 0;
		while (matcher.find(content.pos)) {
			content.pos = matcher.end(1);
			int newLine = content.lineNumber();
			if (newLine >= composedJakLine)
				break;
			line = newLine;
			fileName = matcher.group(1);
		}
		return line;
	}
	
	/**
	 * TODO description/rename
	 * @param composedJakLine 
	 * @param jakContent 
	 * @return
	 * @throws IOException 
	 * @throws CoreException 
	 */
	public int setSourceLine(int composedJakLine, int line, String jakContent) {
		int jakLine = composedJakLine - line + 1;
		try {
			jakLine += numberOfImportLines(jakContent);
		} catch (CoreException e) {
			AheadCorePlugin.getDefault().logError(e);
		} catch (IOException e) {
			AheadCorePlugin.getDefault().logError(e);
		}
		
		/*
		 * Removed because layer declaration is not supported and necessary anymore.
		 * It caused a wrong line calculation.
		 */
//		jakLine += lineNumberOfLayerDeclaration(jakFile);
		return jakLine;
	}

	private int lookupImportInAllJakFiles(String composedJakContent, Matcher matcher) throws CoreException, IOException {
		int a = 0;
		int b = 0;
		for (int i = 0; i < line; i++) {
			if (b < 0)
				return line;
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
					this.file = jakFile;
					return new PosString(text, pos).lineNumber();
				}
			}
		}
		while (matcher.find());
		return line;
	}

	private IFile getJakFile(String filename) {
		String relativeFilename = filename;
		IProject project = file.getProject();
		IFile newFile = project.getFile(relativeFilename.substring(2));
		if (newFile.exists())
			return newFile;
		
//		AheadCorePlugin.getDefault().logWarning("Was not able to locate an error in the source jak file '" + filename + "'");
		return null;
	}

	private static Pattern importPattern = Pattern.compile("(import)\\s[^;\\(\\)\\{\\}\\[\\]]+;");

	private int numberOfImportLines(String contentString) throws CoreException, IOException {
		PosString content = new PosString(contentString);

		Matcher matcher = importPattern.matcher(content.string);
		while (matcher.find(content.pos)) {
			content.pos = matcher.end(1);
		}
		if (content.pos <= 0)
			return 0;
		
		return content.lineNumber() - 1;
	}

//	private int lineNumberOfLayerDeclaration(IFile jakFile) throws CoreException, IOException {
//		jakFile.refreshLocal(IResource.DEPTH_ZERO, null);
//		String contentString = getString(jakFile);
//		PosString content = new PosString(contentString);
//		content.pos = contentString.indexOf("layer");
//		return content.lineNumber() - 1;
//	}

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
    	
    	if (!file.isAccessible()) {
    		return "";
    	}
    	Reader in = null;
    	StringBuilder buffer = new StringBuilder();
    	try {
	        InputStream contentStream = file.getContents();
	        in = new InputStreamReader(contentStream, Charset.availableCharsets().get("UTF-8"));
	
	        int chunkSize = contentStream.available();
	        char[] readBuffer = new char[chunkSize];
	        
	        int n = in.read(readBuffer);
	        while (n > 0) {
	            buffer.append(readBuffer);
	            n = in.read(readBuffer);
	        }
	    } finally {
	    	if (in != null) {
	    		in.close();
	    	}
    	}
        return buffer.toString();
    }

}
