/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.core.builder;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;

import cide.gparser.ParseException;

import composer.FSTGenComposer;
import composer.IParseErrorListener;

import de.ovgu.cide.fstgen.ast.FSTNode;
import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;
import featureide.core.projectstructure.builder.TreeBuilderFeatureHouse;

/**
 * 
 * TODO description
 * 
 * @author Janet Feigenspan
 * @deprecated
 */
public class FeatureHouseBuilder extends IncrementalProjectBuilder implements IParseErrorListener{

	public static final String BUILDER_ID = CorePlugin.PLUGIN_ID + ".featureHouseBuilder";
	
	private IFeatureProject featureProject;
	private String equationPath;
	private String basePath;
	private String outputPath;
	
	private ArrayList<FSTNode> fstNodes = new ArrayList<FSTNode>();
	
	private FSTGenComposer composer = new FSTGenComposer();
	
	private LinkedList<ParseException> parseErrors;


	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.core.internal.events.InternalBuilder#build(int,
	 *      java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
	 */

	private boolean featureProjectLoaded() {
		if (featureProject != null)
			return true;

		featureProject = CorePlugin.getProjectData(getProject());
		if (featureProject == null)
			return false;
		
		return true;		
	}

	protected void clean(IProgressMonitor monitor) throws CoreException {
		if (!featureProjectLoaded())
			return;
		
		fstNodes.clear();

		assert(featureProject != null) : "Variable 'featureProject' should never be null";
		
		if (featureProject.getCurrentEquationFile() == null) {
			CorePlugin.getDefault().logInfo("no equation file found");
			return;
		}
		
		String tmp = featureProject.getCurrentEquationFile().getName();
		
		String equation = tmp.substring(0, tmp.lastIndexOf(".")); 
		CorePlugin.getDefault().logInfo("clean: " + equation);
		if (parseErrors != null)
			parseErrors.clear();
		
		if (composer.getErrorFiles() != null)
			composer.getErrorFiles().clear();

		featureProject.deleteBuilderMarkers(featureProject.getSourceFolder(), IResource.DEPTH_INFINITE);
		
		featureProject.getBinFolder().getFolder(equation).delete(true, monitor);
		featureProject.getBuildFolder().getFolder(equation).delete(true, monitor);
		
		featureProject.getBuildFolder().refreshLocal(IResource.DEPTH_INFINITE, monitor);
		featureProject.getBinFolder().refreshLocal(IResource.DEPTH_INFINITE, monitor);
	}

	@SuppressWarnings("unchecked")
	protected  IProject[] build(int kind, Map args, IProgressMonitor monitor)
			throws CoreException {
		CorePlugin.getDefault().logInfo("build executed");
		
		if (!featureProjectLoaded()) {
			CorePlugin.getDefault().logInfo("feature project not loaded");
			return null;
		}

		featureProject.deleteBuilderMarkers(getProject(), IResource.DEPTH_INFINITE);
		try {
			//TODO replace by change listener, that removes derived resources when their non-derived encounter part is deleted
			clean(monitor);
		} catch (CoreException e) {
			e.printStackTrace();
		}

 		if (featureProject.getCurrentEquationFile() == null) {
			featureProject.createBuilderMarker(getProject(), "No equation file found", 0, IMarker.SEVERITY_WARNING);
			return null;
		}
		

		equationPath = featureProject.getCurrentEquationPath();
		basePath = featureProject.getSourcePath();
		outputPath = featureProject.getBuildPath();

		if (kind == FULL_BUILD) {
			fullBuild(monitor);
		} else {
			IResourceDelta delta = getDelta(getProject());
			if (delta == null) {
				fullBuild(monitor);
			} else {
				incrementalBuild(delta, monitor);
			}
		}
		return null;
	}

	protected void fullBuild(final IProgressMonitor monitor)
			throws CoreException {
//		try {
		CorePlugin.getDefault().logInfo("full building...");
			composer.addParseErrorListener(this);
			composer.run(new String[]{"--expression", equationPath, "--base-directory", basePath,
									  "--output-directory", outputPath + "/"});
			fstNodes = composer.getFstnodes();
			/*
			 * Testing Memory Usage
			 */
//			MemoryTestBench memUsageTest = new MemoryTestBench();
//			memUsageTest.setMemUsageBefore(memUsageTest.memoryUsageWGarbageCol());

			/*
			 * Testing Execution Time
			 */
//			ExecutionTimeTestBench execTest = new ExecutionTimeTestBench();
//			execTest.setStart(System.currentTimeMillis());
//			System.out.println(execTest.getStart());

			TreeBuilderFeatureHouse fstparser = new TreeBuilderFeatureHouse(featureProject.getProjectName());
			fstparser.createProjectTree(fstNodes);
			featureProject.setProjectTree(fstparser.getProjectTree());

//			execTest.setEnd(System.currentTimeMillis());
//			System.out.println(execTest.getEnd());
//			execTest.setDiff(execTest.getEnd() - execTest.getStart());
//			execTest.saveExecTime();
//			System.out.println("diff: " + execTest.getDiff());

//			memUsageTest.setMemUsageAfter(memUsageTest.memoryUsageWOGarbageCol());
//			memUsageTest.setMemUsageDiff(memUsageTest.getMemUsageAfter()
//					- memUsageTest.getMemUsageBefore());
//			memUsageTest.saveMemUsage();

//			featureProject.getProjectTree().print();

			createBuilderMarkers();
//			getProject().accept(new FeatureHouseResourceVisitor());
//		} catch (CoreException e) {
//		}
	}
	
	/**
	 * writes the String outputFST into a file named fileName in the
	 * specified directory. Uses default fileName/directory, if fileName
	 * or directory are <code>null</code>.
	 * @param outputFST the String to be written
	 * @param fileName the fileName of the file that will be created
	 * @param directory the location of the new created file
	 */
	public void saveFST(String outputFST, String fileName, String directory) {

		String fName = "\\FST.txt";
		if (fileName != null) {
			fName = "\\" + fileName + ".txt";
		}
		String fDirectory = "C:\\";
		if (directory != null)
			fDirectory = directory;

		FileWriter fileWriter = null;
		try {
			fileWriter = new FileWriter(new File(fDirectory + fName));
			fileWriter.write(outputFST);
			fileWriter.flush();
			
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		// close the fileWriter
		finally { 
		  if ( fileWriter != null ) 
		    try { fileWriter.close();
		    } catch (IOException e) {
		    	e.printStackTrace();
		    } 
		}
	}

	protected void incrementalBuild(IResourceDelta delta,
			IProgressMonitor monitor) throws CoreException {
		// the visitor does the work.
//		delta.accept(new FeatureHouseDeltaVisitor());
		fullBuild(monitor);
	}

	public void parseErrorOccured(ParseException parseError) {
		if (parseErrors == null)
			parseErrors = new LinkedList<ParseException>();
		
		parseErrors.add(parseError);
		CorePlugin.getDefault().logInfo("Parse Error: " + parseError.getMessage());
	}
	
	public void createBuilderMarkers() {
        Iterator<File> iterateFiles = composer.getErrorFiles().iterator();
        while (iterateFiles.hasNext()) {
        	Iterator<ParseException> iterateErrors = parseErrors.iterator();
        	while (iterateErrors.hasNext()) {

        		ErrorMessage message = new ErrorMessage();

        		// getting the relative path of the files that produced errors
        		IPath projectPath = featureProject.getProject().getLocation();
        		String path = iterateFiles.next().getAbsolutePath();
        		IPath filePath = new Path(path);
        		if (projectPath.isPrefixOf(filePath)) {
        			filePath = filePath.removeFirstSegments(projectPath.segmentCount());
        		}
        		
        		ParseException e = iterateErrors.next();
        		message.setLine(getErrorLineNumber(e));
        		message.setMessage(parseErrorMessage(e.getMessage()));
        		featureProject.createBuilderMarker(getProject().getFile(filePath),
        			message.getMessage(), message.getLine(), IMarker.SEVERITY_ERROR);
        	}
		}
	}

	/**
	 * formats the message to a better readable presentation
	 * @param message the message that should be parsed
	 * @return the formatted message
	 */
	private String parseErrorMessage(String message) {
		StringBuffer msg = new StringBuffer(message);
		for (int i = 0; i < msg.length(); i++) {
			if (msg.charAt(i) == '\n') {
				msg.replace(i-1, i+1, "  ");
			}
		}
		return new String(msg);
	}

	/**
	 * searches the exception message for the line number, in which the error
	 * occured
	 * @param e the exception, in which is searched
	 * @return the line number of the error; or -1, if the line is not found
	 */
	private int getErrorLineNumber(ParseException e) {
		int line = -1;
		if (e.getMessage().contains(" line ")) {
			String [] splittedMessage = e.getMessage().split(" ");
			for (int i = 0; i < splittedMessage.length - 1; i++) {
				if (splittedMessage[i].equals("line")) {
					line = parseLineNumber(splittedMessage[i+1]);
					break;
				}
			}
			return line;
		}
		return line;
	}

	/**
	 * parses the line number from string to int
	 * @param string the string that is parsed
	 * @return the line number of the error; or -1, if the line is not found
	 */
	private int parseLineNumber(String string) {
		int line = -1;
		String []lineNumber = string.split("\\D");
		for (int i = 0; i < lineNumber.length; i++) {
			line = Integer.parseInt(lineNumber[i]);
			break;
		}
		return line;
	}
}

//	class FeatureHouseDeltaVisitor implements IResourceDeltaVisitor {
//		/*
//		 * (non-Javadoc)
//		 * 
//		 * @see org.eclipse.core.resources.IResourceDeltaVisitor#visit(org.eclipse.core.resources.IResourceDelta)
//		 */
//		public boolean visit(IResourceDelta delta) throws CoreException {
////			IResource resource = delta.getResource();
//			switch (delta.getKind()) {
//			case IResourceDelta.ADDED:
//				// handle added resource
//				FSTGenComposer.main(new String[]{"--expression", equationPath, "--base-directory", basePath});
//				break;
//			case IResourceDelta.REMOVED:
//				// handle removed resource
//				FSTGenComposer.main(new String[]{"--expression", equationPath, "--base-directory", basePath});
//				break;
//			case IResourceDelta.CHANGED:
//				// handle changed resource
//				FSTGenComposer.main(new String[]{"--expression", equationPath, "--base-directory", basePath});
//				break;
//			}
//			//return true to continue visiting children.
//			return true;
//		}
//	}
//
//	class FeatureHouseResourceVisitor implements IResourceVisitor {
//		public boolean visit(IResource resource) {
//			FSTGenComposer.main(new String[]{"--expression", equationPath, "--base-directory", basePath});
////			checkXML(resource);
//			//return true to continue visiting children.
//			return true;
//		}
//	}

//	class XMLErrorHandler extends DefaultHandler {
//		
//		private IFile file;
//
//		public XMLErrorHandler(IFile file) {
//			this.file = file;
//		}
//
//		private void addMarker(SAXParseException e, int severity) {
//			FeatureHouseBuilder.this.addMarker(file, e.getMessage(), e
//					.getLineNumber(), severity);
//		}
//
//		public void error(SAXParseException exception) throws SAXException {
//			addMarker(exception, IMarker.SEVERITY_ERROR);
//		}
//
//		public void fatalError(SAXParseException exception) throws SAXException {
//			addMarker(exception, IMarker.SEVERITY_ERROR);
//		}
//
//		public void warning(SAXParseException exception) throws SAXException {
//			addMarker(exception, IMarker.SEVERITY_WARNING);
//		}
//	}

//
//void checkXML(IResource resource) {
//	if (resource instanceof IFile && resource.getName().endsWith(".xml")) {
//		IFile file = (IFile) resource;
//		deleteMarkers(file);
//		XMLErrorHandler reporter = new XMLErrorHandler(file);
//		try {
//			getParser().parse(file.getContents(), reporter);
//		} catch (Exception e1) {
//		}
//	}
//}

//private SAXParser getParser() throws ParserConfigurationException,
//SAXException {
//if (parserFactory == null) {
//parserFactory = SAXParserFactory.newInstance();
//}
//return parserFactory.newSAXParser();
//}
