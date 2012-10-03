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
package de.ovgu.featureide.featurehouse.model;

import java.io.File;
import java.util.ArrayList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Path;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;

/**
 * This builder builds the {@link FSTModel} for FeatureHouse projects, 
 * by parsing the FeatureHouse internal FSTModel.
 * 
 * @author Jens Meinicke
 */
public class FeatureHouseModelBuilder implements FHNodeTypes {

	private FSTModel model;

	private IFeatureProject featureProject;
	
	private FSTFeature currentFeature = null;
	private FSTClass currentClass = null;
	private IFile currentFile = null;

	boolean completeModel = false;

	public FeatureHouseModelBuilder(IFeatureProject featureProject) {
		if (featureProject == null) {
			return;
		}
		FSTModel oldModel = featureProject.getFSTModel();
		if (oldModel != null)
			oldModel.markObsolete();

		model = new FSTModel(featureProject.getProjectName());
		featureProject.setFSTModel(model);
		this.featureProject = featureProject;
	}
	
	public IFile getCurrentFile() {
		return currentFile;
	}
	
	public FSTClass getCurrentClass() {
		return currentClass;
	}

	/**
	 * Builds the model out of the FSTNodes of the FeatureHouse composer
	 * @param nodes The fstNodes
	 * @param completeModel <code>true</code> for completions mode: old methods will not be overwritten
	 */
	@SuppressWarnings("unchecked")
	public void buildModel(ArrayList<FSTNode> nodes, boolean completeModel) {
		this.completeModel = completeModel;
		if (!completeModel) {
			model.reset();
		}
		
		for (FSTNode node : (ArrayList<FSTNode>)nodes.clone()) {
			if (node.getType().equals(NODE_TYPE_FEATURE)) {
				caseAddFeature(node);
			} else if (node.getType().equals(NODE_TYPE_CLASS)) {
				caseAddClass(node);
			} else if (node.getType().equals(JAVA_NODE_CLASS_DECLARATION)) {
				caseClassDeclaration(node);
			} else if (node.getType().equals(C_NODE_SEQUENCE_CODEUNIT_TOPLEVEL)) {
				caseClassDeclaration(node);
			} else if (node.getType().equals(CSHARP_NODE_CLASS_MEMBER_DECLARATION)) {
				caseClassDeclaration(node);
			} else if (node.getType().equals(HASKELL_NODE_DEFINITIONS)) {
				caseClassDeclaration(node);
			} else if (node.getType().equals(HASKELL_NODE_DATA_DECLARATION)) {
				caseClassDeclaration(node);
			}
		}
	}
	
	private void caseAddFeature(FSTNode node) {
		currentFeature = model.addFeature(node.getName());
	}
	
	private void caseAddClass(FSTNode node) {
		String className = node.getName().substring(
				node.getName().lastIndexOf(File.separator) + 1);
		currentFile = getFile(node.getName());
		if (!canCompose()) {
			return;
		}
		
		currentClass = new FSTClass(className);
		currentClass.setClassFile();
		currentClass.setFile(currentFile);
		model.addClass(className, currentFile);
		currentFeature.getClasses().put(className, currentClass);
	}

	private boolean canCompose() {
		return  FeatureHouseComposer.EXTENSIONS
				.contains(currentFile.getFileExtension()) &&
				currentFile.exists();
	}

	private void caseClassDeclaration(FSTNode node) {
		if (node instanceof FSTNonTerminal && canCompose()) {
			for (FSTNode child : ((FSTNonTerminal) node).getChildren()) {
				if (child instanceof FSTTerminal) {
					FSTTerminal terminal = (FSTTerminal) child;
					if (terminal.getType().equals(JAVA_NODE_FIELD)) {
						ClassBuilder.getClassBuilder(currentFile, this)
								.caseFieldDeclaration(terminal);
					} else if (terminal.getType().equals(JAVA_NODE_METHOD)) {
						ClassBuilder.getClassBuilder(currentFile, this)
								.caseMethodDeclaration(terminal);
					} else if (terminal.getType().equals(JAVA_NODE_CONSTRUCTOR)) {
						ClassBuilder.getClassBuilder(currentFile, this)
								.caseConstructorDeclaration(terminal);
					} else if (terminal.getType().equals(C_NODE_FUNC)) {
						ClassBuilder.getClassBuilder(currentFile, this)
							.caseMethodDeclaration(terminal);
					} else if (terminal.getType().equals(C_NODE_STATEMENT)) {
						ClassBuilder.getClassBuilder(currentFile, this)
							.caseFieldDeclaration(terminal);
					} else if (terminal.getType().equals(C_NODE_STMTL)) {
						ClassBuilder.getClassBuilder(currentFile, this)
							.caseFieldDeclaration(terminal);
					} else if (terminal.getType().equals(CSHARP_NODE_CLAASS_MEMBER_DECLARATION_END)) {
						if (terminal.getCompositionMechanism().equals(CSHARP_NODE_COMPOSITON_METHOD)) {
							ClassBuilder.getClassBuilder(currentFile, this)
								.caseMethodDeclaration(terminal);
						} else if (terminal.getCompositionMechanism().equals(CSHARP_NODE_COMPOSITION_FIELD)){
							ClassBuilder.getClassBuilder(currentFile, this)
								.caseFieldDeclaration(terminal);
						} else if (terminal.getCompositionMechanism().equals(CSHARP_NODE_COMPOSITION_CONSTRUCTOR)){
							ClassBuilder.getClassBuilder(currentFile, this)
								.caseConstructorDeclaration(terminal);
						}					
					} else if (terminal.getType().equals(HASKELL_NODE_DECLARATION)) {
						ClassBuilder.getClassBuilder(currentFile, this)
							.caseMethodDeclaration(terminal);
					} else if (terminal.getType().equals(HASKELL_NODE_SIMPLE_TYPE)) {
						ClassBuilder.getClassBuilder(currentFile, this)
							.caseFieldDeclaration(terminal);
					}
				} else if (child instanceof FSTNonTerminal) {
					 if (child.getType().equals(C_NODE_STRUCTDEC)) {
						 caseClassDeclaration(child);
					 } else if (child.getType().equals(JAVA_NODE_INNER_CLASS_TYPE)) {
						 caseClassDeclaration(child);
					 }
				}
			}
		}
	}

	private IFile getFile(String name) {
		String projectName = featureProject.getProjectName();
		name = name.substring(name.indexOf(projectName + "\\" + featureProject.getSourceFolder().getName()) + projectName.length() + 1);
		return featureProject.getProject().getFile(new Path(name));
	}

}
