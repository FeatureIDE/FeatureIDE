/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.refactoring.parser;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.LinkedList;
import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.ui.ahead.AheadUIPlugin;

/**
 * A parser for Jak files.
 * 
 * @author Stephan Kauschka
 */
public class Parser {

    //the location of all source files
    public static final String FILESRC = "src";

    public final static String LINESEPARATOR = System.getProperties().getProperty("line.separator");
    public final static String FILESEPARATOR = System.getProperties().getProperty("file.separator");

    // the parsed File
    private RandomAccessFile raFile;
    private IFile iFile;

    // the project-path of the parsed file
    private String projectPath;

    // the layer-tree which represents the file
    private LayerTree tree;


    public Parser(IFile eqFile) throws Exception {
	this.iFile = eqFile;
	this.projectPath = this.iFile.getProject().getLocation().toOSString();
	this.raFile = new RandomAccessFile(eqFile.getLocation().toOSString(), "r");
	initializeTree();
	resolveProgramCalls();
    }

    /**
     * returns the number of programs inside the file
     */
    public int getNumberOfPrograms() {
	return this.tree.getNumberOfPrograms();
    }

    /**
     * returns the number of layers of program x
     */
    public int getNumberOfLayers(int programNumber) throws Exception {

	if (programNumber < 1 || programNumber > this.tree.getNumberOfPrograms())
	    throw new Exception("program " + programNumber + " does not exist");

	return this.tree.getNumberOfLayers(programNumber);
    }

    /**
     * Returns the number of the program with the given name.
     * If the program does not exist -1 is returned.
     * (Pay attention to the fact, that this method only makes sense
     * parsing equations-files)
     */
    public int getProgramNumber(String programName){
	LinkedList<LayerNode> progs = this.tree.getPrograms();

	int pos=0;
	for(LayerNode node : progs){
	    pos++;
	    if(node.getName().equals(programName))
		return pos;
	}
	return -1;
    }

    /**
     * Returns the number of the layer with the given name.
     * If the layer does not exist -1 is returned.
     * (This method only works for equation-files)
     */
    public int getLayerNumber(String layerName){

	LayerNode root = this.tree.getProgram(1);
	LayerNode node = root.getNext();

	int pos = 0;
	while(node!=null){
	    pos++;
	    if(node.getName().equals(layerName))
		return pos;
	    node = node.getNext();
	}
	return -1;
    }

    /**
     * Returns the number of the layer with the given name.
     * If the layer does not exist -1 is returned.
     * (This method only works for equations-files)
     */
    public int getLayerNumber(String layerName, String programName){

	LayerNode root = this.tree.getProgram(programName);
	LayerNode node = root.getNext();

	int pos = 0;
	while(node!=null){
	    pos++;
	    if(node.getName().equals(layerName))
		return pos;
	    node = node.getNext();
	}
	return -1;
    }

    /**
     * initialises the LayerTree
     */
    private void initializeTree() throws Exception {
	this.tree = new LayerTree();

	if (this.iFile.getFileExtension().equalsIgnoreCase("equation")) {
	    String programName = extractFilenamePrefix(this.iFile.getName());
	    LayerNode node = this.tree.addProgram(programName, 1);
	    LayerNode prev;

	    LinkedList<String> layers = parseLayers();
	    for (String layer : layers) {
		prev = node;
		node = new LayerNode(layer, 0);
		node.setPath(this.iFile.getProject().getLocation().toOSString() + FILESEPARATOR + FILESRC + FILESEPARATOR + layer + FILESEPARATOR);
		prev.setNext(node);
		node.setPrevious(prev);
	    }
	}

	if (this.iFile.getFileExtension().equalsIgnoreCase("equations")) {

	    LinkedList<String> programs = parsePrograms();
	    // the number of the program
	    int i = 0;
	    for (String program : programs) {
		i++;
		String programName = extractProgramname(program);
		LayerNode node = this.tree.addProgram(programName, i);

		LinkedList<String> layers = parseLayers(program);
		LayerNode prev;

		for (String layer : layers) {

		    prev = node;
		    node = new LayerNode(layer, 0);
		    node.setPath(this.iFile.getProject().getLocation().toOSString() + "/"+FILESRC+"/" + layer + "/");
		    prev.setNext(node);
		    node.setPrevious(prev);

		}
	    }
	}
    }

    /**
     * resolves all program-calls inside the LayerTree
     *
     * @throws LoopException
     */
    private void resolveProgramCalls() throws LoopException {

	LinkedList<LayerNode> programs = this.tree.getPrograms();

	for (LayerNode node : programs) {
	    node.setVisited(true);

	    while (node.getNext() != null) {
		LayerNode next = node.getNext();

		if (isProgram(next.getName())) {
		    if (this.tree.getProgram(next.getName()).visited()){
			this.releaseResources();
			throw new LoopException(this.tree.getProgram(next.getName())
				.getNumber());
		    }
		    LayerNode nextProgram = this.tree.getProgram(next.getName());
		    nextProgram.setVisited(true);
		    next.insertCalledProgram(nextProgram);
		} else {
		    node = node.getNext();
		}
	    }
	    this.tree.resetVisits();
	}

    }

    /**
     * extracts the prefix of a filename
     *
     * @param name
     *            the filename
     *
     * @return prefix the extracted prefix
     */
    private static String extractFilenamePrefix(String name) {
	String prefix = "";

	for (int i = 0; i < name.length(); i++) {
	    if (name.charAt(i) != '.')
		prefix = prefix + name.charAt(i);
	    else
		i = name.length();
	}

	return prefix;
    }

    /**
     * extracts the name of a program
     *
     * @param program
     *            the program from which the name has to be extracted
     *
     * @return programName the extracted program-name
     */
    public static String extractProgramname(String program) {
	String programName = "";

	for (int i = 0; i < program.length(); i++) {
	    if (program.charAt(i) != ' ' && program.charAt(i) != '=')
		programName = programName + program.charAt(i);
	    else
		i = program.length();
	}

	return programName;
    }

    /**
     * checks whether a given File is a jak-file
     *
     * @param file
     *            the File that has to be checked
     */
    private static boolean isJakFile(File file) {

	if (!file.isFile())
	    return false;
	if (!file.getName().endsWith(".jak"))
	    return false;

	return true;
    }

    /**
     * checks whether name is a program inside the equations-file
     *
     * @param name
     *            the name that has to be checked
     */
    private boolean isProgram(String name) {

	for (LayerNode n : this.tree.getPrograms()) {
	    if (n.getName().equals(name))
		return true;
	}

	return false;
    }

    /**
     * extracts all layers of an equation-file
     */
    private LinkedList<String> parseLayers() throws Exception {

	this.raFile.seek(0);
	LinkedList<String> layers = new LinkedList<String>();

	// if the equation-file does not contain an equation return
	if (this.raFile.length() <= 0) {
	    throw new Exception(this.projectPath+FILESEPARATOR+FILESRC + " does not contain an equation file");
	}

	String line = this.raFile.readLine();

	// parse layers:
	while (line != null) {

	    // if the line is no comment
	    if (line.length() > 0 && line.charAt(0) != '#')
		layers.add(line);

	    line = this.raFile.readLine();
	}
	;

	return layers;
    }

    /**
     * extracts all layers of a program inside an equations-file
     */
    private LinkedList<String> parseLayers(String program) {

	LinkedList<String> layers = new LinkedList<String>();
	int pos = 0;

	// find begin of first layer
	for (int i = 0; i < program.length(); i++) {
	    if (program.charAt(pos) != '=')
		pos++;
	    else
		i = program.length();
	}

	pos++;

	for (int i = pos; i < program.length(); i++) {
	    if (program.charAt(pos) == ' ')
		pos++;
	    else
		i = program.length();
	}

	// extract layers
	String layer = "";
	for (int i = pos; i < program.length(); i++) {
	    if (program.charAt(i) != ' ')
		layer = layer + program.charAt(i);
	    else {
		if (layer.length() > 0)
		    layers.add(layer);
		layer = "";
	    }
	}

	if (layer.length() > 0)
	    layers.add(layer);

	return layers;
    }

    /**
     * lists all layers of an equation-file
     */
    public LinkedList<String> getLayers(){
	LinkedList<String> layers = new LinkedList<String>();
	LayerNode root = this.tree.getProgram(1);
	LayerNode node = root.getNext();
	while(node != null){
	    layers.add(node.getName());
	    node = node.getNext();
	}
	return layers;
    }

    /**
     * lists all layers of a program inside an equations-file
     */
    public LinkedList<String> getLayers(String program){
	LinkedList<String> layers = new LinkedList<String>();
	LayerNode root = this.tree.getProgram(program);
	LayerNode node = root.getNext();
	while(node != null){
	    layers.add(node.getName());
	    node = node.getNext();
	}
	return layers;
    }

    /**
     * extracts all programs of an equations-file
     */
    public LinkedList<String> parsePrograms() throws Exception {

	this.raFile.seek(0);
	LinkedList<String> programs = new LinkedList<String>();

	// if the equations-file does not contain a program return
	if (this.raFile.length() <= 0) {
	    throw new Exception(this.projectPath+FILESEPARATOR+FILESRC + " does not contain a program");
	}

	String line = this.raFile.readLine();

	// parse programs:
	while (line != null) {

	    // if the line is no comment
	    if (line.length() > 0 && line.charAt(0) != '#')
		programs.add(line);

	    line = this.raFile.readLine();
	}

	return programs;
    }

    /**
     * extracts all jak-files-paths of a given layer and program inside the file
     *
     * @param programNumber
     *            the program from which the jak-file-paths have to be extracted
     *        layerNumber 
     *            the layer from which the jak-file-paths have to be extracted
     *
     * @return list list of all jak-file-paths from the layer
     */
    public LinkedList<String> extractJakFilePaths (int programNumber,
	    int layerNumber) throws Exception {

	if (programNumber < 1 || programNumber > this.tree.getNumberOfPrograms()) {
	    throw new Exception("program " + programNumber + " does not exist");
	}

	LinkedList<String> list = new LinkedList<String>();

	int layers = this.getNumberOfLayers(programNumber);
	if (layerNumber < 1 || layerNumber > layers) {
	    throw new Exception("layer " + layerNumber + " does not exist");
	}

	LayerNode root = this.tree.getProgram(programNumber);
	int pos = 0;
	while (pos < layerNumber)
	    if (root.getNext() != null) {
		pos++;
		root = root.getNext();
	    }

	File directory = new File(root.getPath());
	if (!directory.exists())
	    throw new Exception("directory " + root.getPath() + " does not exist");

	File[] fileList = directory.listFiles();

	if (fileList != null) {
	    for (File f : fileList)
		if (isJakFile(f))
		    list.add(f.getAbsolutePath());
	} else
	    throw new Exception("directory " + root.getPath() + " contains no files");

	return list;
    }

    /**
     * returns the layername of a given layer and program inside the file
     *
     * @param programNumber
     *            the program in which the layer is specified
     *        layerNumber 
     *            the layer from which the name shall be returned
     *
     * @return name the layername
     */
    public String getLayerName(int programNumber, int layerNumber) throws Exception {
	String name = "";
	if (programNumber < 1 || programNumber > this.tree.getNumberOfPrograms()) {
	    throw new Exception("program " + programNumber + " does not exist");
	}

	int layers = this.getNumberOfLayers(programNumber);
	if (layerNumber < 1 || layerNumber > layers) {
	    throw new Exception("layer " + layerNumber + " does not exist");
	}

	LayerNode root = this.tree.getProgram(programNumber);
	int pos = 0;
	while (pos < layerNumber)
	    if (root.getNext() != null) {
		pos++;
		root = root.getNext();
	    }

	name = root.getName();
	return name;
    }

    /**
     * When the current parser is not used any more its equation[s]-file has to
     * be released for further use, i.e. the randomaccessfile has to be closed.
     * The parser can't be used afterwards again.
     */
    public void releaseResources(){
	try {
	    raFile.close();
        } catch (IOException e) {
	    AheadUIPlugin.getDefault().logError(e);
        }
    }

}
