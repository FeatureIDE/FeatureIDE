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
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
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
	
	private FSTRole currentRole = null;
	private IFile currentFile = null;

	boolean completeModel = false;

	private FSTFeature currentFeature;

	public FeatureHouseModelBuilder(IFeatureProject featureProject) {
		if (featureProject == null) {
			return;
		}
		model = new FSTModel(featureProject);
		featureProject.setFSTModel(model);
		this.featureProject = featureProject;
	}
	
	public IFile getCurrentFile() {
		return currentFile;
	}
	
	public FSTRole getCurrentRole() {
		return currentRole;
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
			if (NODE_TYPE_FEATURE.equals(node.getType())) {
				caseAddFeature(node);
			} else if (NODE_TYPE_CLASS.equals(node.getType())) {
				caseAddClass(node);
			} else if (JAVA_NODE_CLASS_DECLARATION.equals(node.getType())) {
				caseClassDeclaration(node);
			} else if (C_NODE_SEQUENCE_CODEUNIT_TOPLEVEL.equals(node.getType())) {
				caseClassDeclaration(node);
			} else if (CSHARP_NODE_CLASS_MEMBER_DECLARATION.equals(node.getType())) {
				caseClassDeclaration(node);
			} else if (HASKELL_NODE_DEFINITIONS.equals(node.getType())) {
				caseClassDeclaration(node);
			} else if (HASKELL_NODE_DATA_DECLARATION.equals(node.getType())) {
				caseClassDeclaration(node);
			}
		}
	}
	
	private void caseAddFeature(FSTNode node) {
		currentFeature = model.addFeature(node.getName());
	}
	
	private void caseAddClass(FSTNode node) {
		String name = node.getName();
		String className = name.substring(
				name.lastIndexOf(File.separator) + 1);
		currentFile = getFile(name);
		if (!canCompose()) {
			return;
		}
		currentRole = model.addRole(currentFeature.getName(), className, currentFile);
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
					if (JAVA_NODE_FIELD.equals(terminal.getType())) {
						ClassBuilder.getClassBuilder(currentFile, this)
								.caseFieldDeclaration(terminal);
					} else if (JVVA_NODE_FIELD_2.equals(terminal.getType())) {
							ClassBuilder.getClassBuilder(currentFile, this)
									.caseFieldDeclaration(terminal);	 
					} else if (JAVA_NODE_METHOD.equals(terminal.getType())) {
						ClassBuilder.getClassBuilder(currentFile, this)
								.caseMethodDeclaration(terminal);
					} else if (JAVA_NODE_CONSTRUCTOR.equals(terminal.getType())) {
						ClassBuilder.getClassBuilder(currentFile, this)
								.caseConstructorDeclaration(terminal);
					} else if (C_NODE_FUNC.equals(terminal.getType())) {
						ClassBuilder.getClassBuilder(currentFile, this)
							.caseMethodDeclaration(terminal);
					} else if (C_NODE_STATEMENT.equals(terminal.getType())) {
						ClassBuilder.getClassBuilder(currentFile, this)
							.caseFieldDeclaration(terminal);
					} else if (C_NODE_STMTL.equals(terminal.getType())) {
						ClassBuilder.getClassBuilder(currentFile, this)
							.caseFieldDeclaration(terminal);
					} else if (CSHARP_NODE_CLAASS_MEMBER_DECLARATION_END.equals(terminal.getType())) {
						if (CSHARP_NODE_COMPOSITON_METHOD.equals(terminal.getCompositionMechanism())) {
							ClassBuilder.getClassBuilder(currentFile, this)
								.caseMethodDeclaration(terminal);
						} else if (CSHARP_NODE_COMPOSITION_FIELD.equals(terminal.getCompositionMechanism())){
							ClassBuilder.getClassBuilder(currentFile, this)
								.caseFieldDeclaration(terminal);
						} else if (CSHARP_NODE_COMPOSITION_CONSTRUCTOR.equals(terminal.getCompositionMechanism())){
							ClassBuilder.getClassBuilder(currentFile, this)
								.caseConstructorDeclaration(terminal);
						}					
					} else if (HASKELL_NODE_DECLARATION.equals(terminal.getType())) {
						ClassBuilder.getClassBuilder(currentFile, this)
							.caseMethodDeclaration(terminal);
					} else if (HASKELL_NODE_SIMPLE_TYPE.equals(terminal.getType())) {
						ClassBuilder.getClassBuilder(currentFile, this)
							.caseFieldDeclaration(terminal);
					} else if (JML_SPEC_CASE_SEQ.equals(terminal.getType())) {
						ClassBuilder.getClassBuilder(currentFile, this)
						.caseJMLSpecCaseSeq(terminal);
					}
				} else if (child instanceof FSTNonTerminal) {
					caseClassDeclaration(child);
				}
			}
		}
	}

	private IFile getFile(String name) {
		String projectName = featureProject.getProjectName();
		name = name.substring(name.indexOf(projectName + System.getProperty("file.separator") + featureProject.getSourceFolder().getName()) + projectName.length() + 1);
		return featureProject.getProject().getFile(new Path(name));
	}

}
