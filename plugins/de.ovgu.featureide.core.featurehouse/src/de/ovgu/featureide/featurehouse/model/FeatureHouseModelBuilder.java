/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.model;

import java.io.File;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;
import de.ovgu.cide.fstgen.ast.FSTVisitor;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.fm.core.base.FeatureUtils;

/**
 * This builder builds the {@link FSTModel} for FeatureHouse projects, by parsing the FeatureHouse internal FSTModel.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureHouseModelBuilder implements FHNodeTypes {

	private FSTModel model;

	private IFeatureProject featureProject;

	private final LinkedList<FSTClassFragment> classFragmentStack = new LinkedList<FSTClassFragment>();
	private FSTRole currentRole = null;
	private IFile currentFile = null;

	private FSTFeature currentFeature;

	public FeatureHouseModelBuilder(IFeatureProject featureProject) {
		if (featureProject == null) {
			return;
		}
		model = featureProject.getFSTModel();
		if (model == null) {
			model = new FSTModel(featureProject);
		}
		featureProject.setFSTModel(model);
		this.featureProject = featureProject;
	}

	public IFile getCurrentFile() {
		return currentFile;
	}

	public FSTRole getCurrentRole() {
		return currentRole;
	}

	public FSTClassFragment getCurrentClassFragment() {
		final FSTClassFragment currentClassFragment = classFragmentStack.peek();
		return (currentClassFragment == null) ? currentRole.getClassFragment() : classFragmentStack.peek();
	}

	public boolean hasCurrentClassFragment() {
		return (currentRole != null) || (classFragmentStack.peek() != null);
	}

	/**
	 * Builds the model out of the FSTNodes of the FeatureHouse composer
	 *
	 * @param nodes The fstNodes
	 * @param completeModel <code>true</code> for completions mode: old methods will not be overwritten
	 */
	@SuppressWarnings("unchecked")
	public void buildModel(ArrayList<FSTNode> nodes, boolean completeModel) {
		if (nodes == null) {
			FeatureHouseCorePlugin.getDefault().logError("FST could not be build!", null);
		}
		if (!completeModel) {
			model.reset();
		}
		for (final FSTNode node : (ArrayList<FSTNode>) nodes.clone()) {
			if (NODE_TYPE_FEATURE.equals(node.getType())) {
				caseAddFeature(node);
			} else if (NODE_TYPE_CLASS.equals(node.getType())) {
				caseAddClass(node);
			} else if (NODE_COMPILATIONUNIT.equals(node.getType())) {
				caseCompileUnit(node);
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
			} else if (ASMETAL_MODULE_DECLARATION.equals(node.getType())) {
				caseClassDeclaration(node);
			}

			addArbitraryFiles();
		}
	}

	private void addArbitraryFiles() {
		final IFolder folder = featureProject.getSourceFolder();
		for (final String feature : FeatureUtils.extractConcreteFeaturesAsStringList(featureProject.getFeatureModel())) {
			final IFolder featureFolder = folder.getFolder(feature);
			if (featureFolder.isAccessible()) {
				addArbitraryFiles(featureFolder, feature);
			}
		}
	}

	private void addArbitraryFiles(IFolder featureFolder, String feature) {
		try {
			for (final IResource res : featureFolder.members()) {
				if (res instanceof IFolder) {
					addArbitraryFiles((IFolder) res, feature);
				} else if (res instanceof IFile) {
					if (!featureProject.getComposer().extensions().contains(res.getFileExtension())) {
						model.addArbitraryFile(feature, (IFile) res);
					}
				}
			}
		} catch (final CoreException e) {
			FeatureHouseCorePlugin.getDefault().logError(e);
		}
	}

	private void caseCompileUnit(FSTNode node) {
		node.accept(new FSTVisitor() {

			@Override
			public boolean visit(FSTTerminal terminal) {
				if (JAVA_NODE_IMPORTDECLARATION.equals(terminal.getType())) {
					ClassBuilder.getClassBuilder(currentFile, FeatureHouseModelBuilder.this).caseAddImport(terminal);
				} else if (JAVA_NODE_PACKAGEDECLARATION.equals(terminal.getType())) {
					ClassBuilder.getClassBuilder(currentFile, FeatureHouseModelBuilder.this).casePackage(terminal);
				}
				return true;
			}
		});
	}

	private void caseAddFeature(FSTNode node) {
		currentFeature = model.addFeature(node.getName());
	}

	private void caseAddClass(FSTNode node) {
		currentFile = getFile(node.getName());
		if (!canCompose()) {
			return;
		}
		currentRole = model.addRole(currentFeature.getName(), model.getAbsoluteClassName(currentFile), currentFile);
		// create directives?? class added ppmodelbuilder
		classFragmentStack.clear();
		classFragmentStack.push(currentRole.getClassFragment());
	}

	private boolean canCompose() {
		if (currentFile == null) {
			return false;
		}
		return FeatureHouseComposer.EXTENSIONS.contains(currentFile.getFileExtension()) && currentFile.exists();
	}

	private void caseClassDeclaration(FSTNode node) {
		if ((node instanceof FSTNonTerminal) && canCompose()) {
			final List<FSTNode> children = ((FSTNonTerminal) node).getChildren();
			for (final FSTNode child : children) {

				final String type = child.getType();
				final ClassBuilder classBuilder = ClassBuilder.getClassBuilder(currentFile, this);
				if (child instanceof FSTTerminal) {
					final FSTTerminal terminal = (FSTTerminal) child;
					if (JAVA_NODE_DECLARATION_TYPE1.equals(type) || JAVA_NODE_DECLARATION_TYPE2.equals(type)) {
						classBuilder.caseClassDeclarationType(terminal);
					} else if (JAVA_NODE_MODIFIERS.equals(type)) {
						classBuilder.caseModifiers(terminal);
						if (classFragmentStack.peek() != null) {
							classFragmentStack.peek().setJavaDocComment(JavaClassBuilder.findJavaDocComments(terminal));
						}
					} else if (JAVA_NODE_EXTENDSLIST.equals(type)) {
						classBuilder.caseExtendsList(terminal);
					} else if (JAVA_NODE_IMPLEMENTATIONLIST.equals(type)) {
						classBuilder.caseImplementsList(terminal);
					} else if (JAVA_NODE_FIELD.equals(type)) {
						classBuilder.caseFieldDeclaration(terminal);
					} else if (JAVA_NODE_FIELD_2.equals(type)) {
						classBuilder.caseFieldDeclaration(terminal);
					} else if (JAVA_NODE_FIELD_3.equals(type)) {
						classBuilder.caseFieldDeclaration(terminal);
					} else if (JAVA_NODE_METHOD.equals(type)) {
						classBuilder.caseMethodDeclaration(terminal);
					} else if (JAVA_NODE_CONSTRUCTOR.equals(type)) {
						classBuilder.caseConstructorDeclaration(terminal);
					} else if (C_NODE_FUNC.equals(type)) {
						classBuilder.caseMethodDeclaration(terminal);
					} else if (C_NODE_STATEMENT.equals(type)) {
						classBuilder.caseFieldDeclaration(terminal);
					} else if (C_NODE_STMTL.equals(type)) {
						classBuilder.caseFieldDeclaration(terminal);
					} else if (CSHARP_NODE_CLAASS_MEMBER_DECLARATION_END.equals(type)) {
						if (CSHARP_NODE_COMPOSITON_METHOD.equals(terminal.getCompositionMechanism())) {
							classBuilder.caseMethodDeclaration(terminal);
						} else if (CSHARP_NODE_COMPOSITION_FIELD.equals(terminal.getCompositionMechanism())) {
							classBuilder.caseFieldDeclaration(terminal);
						} else if (CSHARP_NODE_COMPOSITION_CONSTRUCTOR.equals(terminal.getCompositionMechanism())) {
							classBuilder.caseConstructorDeclaration(terminal);
						}
					} else if (HASKELL_NODE_DECLARATION.equals(type)) {
						classBuilder.caseMethodDeclaration(terminal);
					} else if (HASKELL_NODE_SIMPLE_TYPE.equals(type)) {
						classBuilder.caseFieldDeclaration(terminal);
					} else if (JML_SPEC_CASE_SEQ.equals(type)) {
						classBuilder.caseJMLSpecCaseSeq(terminal);
					} else if (JML_INVARIANT.equals(type)) {
						classBuilder.caseInvariant(terminal);
					} else if (ASMETAL_NAMED_INVARIANT.equals(type)) {
						classBuilder.caseInvariant(terminal);
					} else if (ASMETAL_UNNAMED_INVARIANT.equals(type)) {
						classBuilder.caseInvariant(terminal);
					} else if (FHNodeTypes.ASMETAL_RULE.equals(type)) {
						classBuilder.caseMethodDeclaration(terminal);
					}
				} else if (child instanceof FSTNonTerminal) {
					if (JAVA_NODE_INNER_CLASS_TYPE.equals(type)) {
						final String name = child.getName();
						final String className = name.substring(name.lastIndexOf(File.separator) + 1);

						final FSTClassFragment newFragment = new FSTClassFragment(className);
						if (classFragmentStack.peek() != null) {
							newFragment.setRole(classFragmentStack.peek().getRole());
							newFragment.setInnerClass(true);
						}
						classFragmentStack.push(newFragment);
					} else if (ASMETAL_SIGNATURE.equals(type)) {
						classBuilder.caseSignatureDeclaration((FSTNonTerminal) child);
					} else if (ASMETAL_INITIALIZATION.equals(type)) {
						classBuilder.caseInitialization(child);
					} else {
						classFragmentStack.push(classFragmentStack.peek());
					}
					caseClassDeclaration(child);
				}
			}

			if (!classFragmentStack.isEmpty()) {
				final FSTClassFragment lastElement = classFragmentStack.pop();
				if (lastElement != null) {
					final FSTClassFragment nextElement = classFragmentStack.peek();
					if (lastElement.isInnerClass() && (nextElement != null) && !lastElement.equals(nextElement)) {
						classFragmentStack.peek().add(lastElement);
					}
				}
			}
		}
	}

	private IFile getFile(String name) {
		final IProject project = featureProject.getProject();
		final IPath rl = project.getRawLocation();
		final String projectName;
		if (rl != null) {
			projectName = rl.toOSString();
		} else {
			projectName = featureProject.getProjectName();
		}
		if ((name.indexOf(projectName + System.getProperty("file.separator") + featureProject.getSourceFolder().getName()) == -1)) {
			return null;
		}
		name = name.substring(
				name.indexOf(projectName + System.getProperty("file.separator") + featureProject.getSourceFolder().getName()) + projectName.length() + 1);
		return featureProject.getProject().getFile(new Path(name));
	}

}
