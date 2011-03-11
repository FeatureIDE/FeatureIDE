/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.featurehouse.model;

import java.io.File;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Path;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.IFSTModel;
import de.ovgu.featureide.core.fstmodel.oomodel.Class;
import de.ovgu.featureide.core.fstmodel.oomodel.Feature;
import de.ovgu.featureide.core.fstmodel.oomodel.Field;
import de.ovgu.featureide.core.fstmodel.oomodel.Method;
import de.ovgu.featureide.core.fstmodel.oomodel.OOModel;


/**
 * This builder builds the JavaProjectModel, by extracting features, 
 * methods and fields from classes to build. 
 * 
 * @author Jens Meinicke
 */
public class FeatureHouseModelBuilder {

	private OOModel model;
	private IFeatureProject featureProject;
	
	private static final String NODE_TYPE_FEATURE = "Feature";
	private static final String NODE_TYPE_CLASS = "EOF Marker";
	private static final String NODE_TYPE_CLASS_DECLARATION = "ClassDeclaration";
	private static final String NODE_TYPE_FIELD = "FieldDecl";
	private static final String NODE_TYPE_METHOD = "MethodDecl";
	private static final String NODE_TYPE_CONSTRUCTOR = "ConstructorDecl";
	
	public FeatureHouseModelBuilder(IFeatureProject featureProject) {
		IFSTModel oldModel = featureProject.getFSTModel();
		if (oldModel != null)
			oldModel.markObsolete();

		model = new OOModel(featureProject.getProjectName());
		featureProject.setFSTModel(model);
		this.featureProject = featureProject;
	}

	public void buildModel(List<FSTNode> nodes) {
		model.classesMap = new HashMap<IFile, Class>();
		model.classes = new HashMap<String, Class>();
		model.features = new HashMap<String, Feature>();
		
		Feature currentFeature = null;
		Class currentClass = null;
		IFile currentFile = null;
		
		for (FSTNode node : nodes) {
			if (node.getType().equals(NODE_TYPE_FEATURE)) {
				// case: new feature
				if (currentFeature != null && model.features.containsKey(node.getName())) {
					currentFeature = model.features.get(node.getName());
				} else {
					currentFeature = new Feature(node.getName());
					model.features.put(node.getName(), currentFeature);
				}
			} else if (node.getType().equals(NODE_TYPE_CLASS)) {
				// case: new class
				String className = node.getName().substring(
						node.getName().lastIndexOf(File.separator) + 1);
				currentClass = new Class(className);
				currentFile = getFile(node.getName());
				currentClass.setFile(currentFile);
				model.classes.put(className, currentClass);
				addClass(className, node.getName());
				currentFeature.classes.put(className, currentClass);
			} else if (node.getType().equals(NODE_TYPE_CLASS_DECLARATION)) {
				// case: class declaration
				if (node instanceof FSTNonTerminal) {
					FSTNonTerminal nonterminal = (FSTNonTerminal) node;
					for (FSTNode child : nonterminal.getChildren()) {
						if (child instanceof FSTTerminal) {
							FSTTerminal terminal = (FSTTerminal) child;
							if (terminal.getType().equals(NODE_TYPE_FIELD)) {
								// case: field declaration
								String body = terminal.getBody().substring(0,
										terminal.getBody().indexOf(terminal.getName()));
								
								// get type
								String type = null;
								if (!body.contains("<")) {
									type = body.split("[ ]")[body.split("[ ]").length -1];
								} else {
									for (String t : body.split("[ ]")) {
										if (type != null) {
											type = type + " " + t;
										} else if (t.contains("<")) {
											type = t;
										}
									}
								}
								
								// get modifiers
								String modifiers = "";
								if (body.indexOf(type) != 0) {
									modifiers = body.substring(0, body.indexOf(type)-1);
								}
								
								// get name(s)
								String[] fields = {terminal.getName()};
								if (!terminal.getBody().contains("=")) {
									fields = terminal.getBody().substring(terminal.getBody().indexOf(
										terminal.getName()), terminal.getBody().length() - 1).split("[,]");
								}
								for (String f : fields) {
									f = f.replace("\n", "");
									f = f.replace("\r", "");
									while (f.startsWith(" ")) {
										f = f.substring(1);
									}
									
									// add field
									Field field = new Field(f,type,0,modifiers);
									field.setOwn(currentFile);
									currentClass.fields.put(field.getIdentifier(), field);
								}
							} else if (terminal.getType().equals(NODE_TYPE_METHOD)) {
								// case: method declaration
								// get name
								String name = terminal.getName().substring(0,
										terminal.getName().indexOf("("));
								
								// get return type
								String body = terminal.getBody().substring(0, terminal.getBody().indexOf(name));
								String returnType = body.split("[ ]")[body.split("[ ]").length -1];
								
								// get modifiers
								String modifiers = "";
								if (body.indexOf(returnType) != 0) {
									modifiers = body.substring(0, body.indexOf(returnType)-1);
								}
								
								// get parameter types
								String parameter = terminal.getName().substring(terminal.getName().indexOf("(") + 1, terminal.getName().indexOf(")"));
								LinkedList<String> parameterTypes = new LinkedList<String>();
								if (!parameter.equals("") && !parameter.startsWith("{")) {
									String[] p = parameter.split("[-]");
									for (int i = 0; i < p.length; i+=2) {
										parameterTypes.add(p[i]);
										
									}
								}
								
								// add method
								Method method = new Method(name, parameterTypes, returnType, modifiers);								
								method.setOwn(currentFile);
								currentClass.methods.put(method.getIdentifier(), method);
							} else if (terminal.getType().equals(NODE_TYPE_CONSTRUCTOR)) {
								// case: constructor declaration
								// get name
								String name = terminal.getName().substring(0,
										terminal.getName().indexOf("("));
								
								// get modifiers
								String modifiers = "";
								if (terminal.getBody().indexOf(name) > 0) {
									modifiers = terminal.getBody().substring(0, terminal.getBody().indexOf(name) - 1);
								}
								
								// get parameter types
								String parameter = terminal.getName().substring(
										terminal.getName().indexOf("(") + 1, terminal.getName().indexOf(")"));
								LinkedList<String> parameterTypes = new LinkedList<String>();
								if (!parameter.equals("") && !parameter.startsWith("{")) {
									String[] p = parameter.split("[-]");
									for (int i = 0; i < p.length; i+=2) {
										parameterTypes.add(p[i]);
									}
								}
								
								// add constructor
								Method constructor = new Method(name, parameterTypes, "void", modifiers);
								constructor.setOwn(currentFile);
								currentClass.methods.put(constructor.getIdentifier(), constructor);
							}
						}
					}
				}
			}
		}
	}
	
	/**
	 * @param name
	 * @return
	 */
	private IFile getFile(String name) {
		String projectName = featureProject.getProjectName();
		name = name.substring(name.indexOf(projectName) + projectName.length() + 1);
		return featureProject.getProject().getFile(new Path(name));
	}

	/**
	 * Adds a class to the java project model
	 * 
	 */
	public void addClass(String className, String source) {
		Class currentClass = null;
		
		if (model.classes.containsKey(className)) {
			currentClass = model.classes.get(className);
		} else {
			currentClass = new Class(className);
			model.classes.put(className, currentClass);
		}
		if (!model.classesMap.containsKey(source)) {
			
			model.classesMap.put(null, currentClass);
		}
	}

}
