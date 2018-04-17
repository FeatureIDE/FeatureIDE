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
package de.ovgu.featureide.fm.core.io.velvet;

import static de.ovgu.featureide.fm.core.localization.StringTable.ILLEGAL_SYNTAX_IN_LINE;
import static de.ovgu.featureide.fm.core.localization.StringTable.IN_FILE;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_ALREADY_IN_USE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_ALREADY_USED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_SUCH_ATTRIBUTE_DEFINED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_PARENT_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_VARIABLE_NAME;
import static java.lang.String.format;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.Map.Entry;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.CommonErrorNode;
import org.antlr.runtime.tree.Tree;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.prop4j.And;
import org.prop4j.Choose;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.ModelMarkerHandler;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.ExtendedConstraint;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModel.UsedModel;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.constraint.Equation;
import de.ovgu.featureide.fm.core.constraint.FeatureAttribute;
import de.ovgu.featureide.fm.core.constraint.Reference;
import de.ovgu.featureide.fm.core.constraint.ReferenceType;
import de.ovgu.featureide.fm.core.constraint.RelationOperator;
import de.ovgu.featureide.fm.core.constraint.WeightedTerm;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * Parses a feature model in Velvet syntax.
 *
 * @deprecated Use {@link VelvetFeatureModelFormat} and {@link FileHandler} instead.
 *
 * @author Sebastian Krieter
 * @author Matthias Strauss
 * @author Marcus Pinnecke (Feature Interface)
 */
@Deprecated
public class VelvetFeatureModelReader extends AbstractFeatureModelReader {

	private static class ConstraintNode {

		private final Node computedNode;
		private final Tree rawNode;

		public ConstraintNode(Node computedNode, Tree rawNode) {
			this.computedNode = computedNode;
			this.rawNode = rawNode;
		}
	}

	private static final ExtendedFeatureModelFactory factory = ExtendedFeatureModelFactory.getInstance();

	private static final int[] binaryOperators =
		{ VelvetParser.OP_OR, VelvetParser.OP_AND, VelvetParser.OP_XOR, VelvetParser.OP_IMPLIES, VelvetParser.OP_EQUIVALENT };
	private static final String[] paths = { "%s.velvet", "%s.xml", "MPL/%s.velvet" };

	private final LinkedList<Tree> atrributeConstraintNodes = new LinkedList<Tree>();
	private final LinkedList<IFeature> parentStack = new LinkedList<IFeature>();
	private final LinkedList<ConstraintNode> constraintNodeList = new LinkedList<ConstraintNode>();
	private final HashSet<String> usedVariables = new HashSet<String>();

	private final boolean velvetImport;

	private ModelMarkerHandler<IResource> modelMarkerHandler;
	private final ExtendedFeatureModel extFeatureModel;
	private String extFeatureModelName;
	private boolean localSearch = false;

	/**
	 * Reads external model with the right FeatureModelReader.
	 *
	 * @param file file of feature model
	 * @return the feature model or null if error occurred
	 */
	private IFeatureModel readExternalModelFile(File file) {
		return FeatureModelManager.load(file.toPath()).getObject();
	}

	private boolean checkExternalModelFile(Tree curNode) {
		if (localSearch) {
			if (localSearch(curNode.getText()) == null) {
				reportWarning(curNode, format("No model for %s could be found.", curNode.getText()));
				return false;
			}
			return true;
		}
		if (getExternalModelFile(curNode.getText()) == null) {
			reportWarning(curNode, format("No model for %s could be found.", curNode.getText()));
			return false;
		}
		return true;
	}

	private boolean checkInterfaceModelFile(Tree curNode) {
		if (localSearch) {
			if (localSearch(curNode.getText()) == null) {
				reportWarning(curNode, format("No model for %s could be found.", curNode.getText()));
				return false;
			}
			return true;
		}
		if (getInterfaceModelFile(curNode.getText()) == null) {
			reportWarning(curNode, format("No interface for %s could be found.", curNode.getText()));
			return false;
		}
		return true;
	}

	private void copyChildnodes(final ExtendedFeatureModel targetModel, final IFeatureStructure targetParentNode, final IFeatureStructure sourceParentNode,
			final String parentModelName, final String parentNodeName, final int type) {
		for (final IFeatureStructure child : sourceParentNode.getChildren()) {
			final ExtendedFeature feature;
			if (velvetImport) {
				feature = factory.createFeature(targetModel, child.getFeature().getName());
			} else {
				feature = factory.createFeature(targetModel, parentNodeName + "." + child.getFeature().getName());
			}
			final IFeatureStructure featureStructure = feature.getStructure();
			featureStructure.setMandatory(child.isMandatory());
			featureStructure.setAbstract(child.isAbstract());
			featureStructure.setHidden(child.isHidden());
			feature.setExternalModelName(parentModelName);

			featureStructure.setAND(child.isAnd());
			featureStructure.setMultiple(child.isMultiple());
			if (child.isOr()) {
				featureStructure.setOr();
			}

			targetModel.addFeature(feature);
			targetParentNode.addChild(featureStructure);
			feature.setType(type);

			if (child.hasChildren()) {
				copyChildnodes(targetModel, featureStructure, child, parentModelName, parentNodeName, type);
			}
		}
	}

	private static WeightedTerm createTerm(final int weight, final boolean rightSide, final boolean minus, final Reference reference) {
		boolean positive = weight >= 0;
		if (rightSide ^ minus) {
			positive = !positive;
		}
		return new WeightedTerm(Math.abs(weight), positive, reference);
	}

	private static LinkedList<Tree> getChildren(final Tree root) {
		final LinkedList<Tree> children = new LinkedList<Tree>();

		final int childCount = root.getChildCount();
		for (int i = 0; i < childCount; i++) {
			children.add(root.getChild(i));
		}
		return children;
	}

	private static void updateConstraintNode(Node curNode, String parentModelname, String rootName) {
		if (curNode instanceof Literal) {
			final Literal literal = (Literal) curNode;
			if (literal.var.equals(rootName)) {
				literal.var = parentModelname;
			} else {
				literal.var = parentModelname + "." + literal.var.toString();
			}
		} else {
			for (final Node child : curNode.getChildren()) {
				updateConstraintNode(child, parentModelname, rootName);
			}
		}
	}

	public VelvetFeatureModelReader(final IFeatureModel featureModel) {
		this(featureModel, false);
	}

	public VelvetFeatureModelReader(final IFeatureModel featureModel, boolean velvetImport) {
		extFeatureModel = (ExtendedFeatureModel) featureModel;
		setFeatureModel(extFeatureModel);
		this.velvetImport = velvetImport;
	}

	@Override
	protected synchronized void parseInputStream(final InputStream inputStream) throws UnsupportedModelException {
		ANTLRInputStream antlrInputStream = null;
		try {
			antlrInputStream = new ANTLRInputStream(inputStream);
		} catch (final IOException e) {
			Logger.logError(e);
			throw new UnsupportedModelException("Error while reading model!", 0);
		}
		final VelvetParser parser = new VelvetParser(new CommonTokenStream(new VelvetLexer(antlrInputStream)));
		Tree root = null;
		try {
			root = (Tree) parser.velvetModel().getTree();
			if (root == null) {
				throw new UnsupportedModelException("Error while parsing model!", 0);
			}
			init();

			checkTree(root);
			parseModel(root);
			parseAttributeConstraints();
		} catch (final RecognitionException e) {
			Logger.logError(e);
			throw new UnsupportedModelException(e.getMessage(), e.line);
		}

		// Update the FeatureModel in Editor
		extFeatureModel.handleModelDataLoaded();
	}

	private ExtendedFeature addFeature(final IFeature parent, final String featureName, final boolean isMandatory, final boolean isAbstract,
			final boolean isHidden) {
		final ExtendedFeature newFeature = factory.createFeature(extFeatureModel, featureName);
		newFeature.getStructure().setMandatory(isMandatory);
		newFeature.getStructure().setAbstract(isAbstract);
		newFeature.getStructure().setHidden(isHidden);

		final IFeature orgFeature = extFeatureModel.getFeature(featureName);
		if ((orgFeature != null) && (orgFeature instanceof ExtendedFeature)) {
			return (ExtendedFeature) orgFeature;
		} else {
			extFeatureModel.addFeature(newFeature);
			parent.getStructure().addChild(newFeature.getStructure());
			newFeature.setNewDefined(true);
			return newFeature;
		}
	}

	private String checkNode(Node curNode) {
		if (curNode instanceof Literal) {
			final Literal literal = (Literal) curNode;
			final String varString = literal.var.toString();
			if (extFeatureModel.getFeature(varString) == null) {
				return literal.var.toString();
			}
		} else {
			for (final Node child : curNode.getChildren()) {
				final String childRet = checkNode(child);
				if (childRet != null) {
					return childRet;
				}
			}
		}
		return null;
	}

	private IFeatureModel getExternalFeatureModel(Tree curNode) {
		final File modelFile = getExternalModelFile(curNode.getText());
		if (modelFile == null) {
			reportWarning(curNode, format("No model for %s could be found.", curNode.getText()));
			return null;
		}
		return readModel(modelFile, curNode);
	}

	private IFeatureModel getExternalFeatureModel(String modelName, Tree curNode) {
		final File modelFile = getExternalModelFile(modelName);
		if (modelFile == null) {
			return null;
		}
		return readModel(modelFile, curNode);
	}

	private IFeatureModel getInterfaceFeatureModel(String modelName, Tree curNode) {
		final File modelFile = getInterfaceModelFile(modelName);
		if (modelFile == null) {
			return null;
		}
		return readModel(modelFile, curNode);
	}

	private IFeatureModel readModel(File modelFile, Tree curNode) {
		final IFeatureModel fm = readExternalModelFile(modelFile);
		if (fm == null) {
			reportWarning(curNode, format("External model for %s could not be read.", curNode.getText()));
			return null;
		}
		return fm;
	}

	/**
	 * Search for the right File to include etc. The following search path is used: <ol> <li>./NAME.velvet</li> <li>./NAME.xml</li> <li>./MPL/NAME.velvet</li>
	 * <li>/NAME_AS_PROJECT/model.xml</li> </ol>
	 *
	 * @param name the name of file or project
	 * @return File object if found else null
	 */
	private File getExternalModelFile(String name) {
		if (localSearch) {
			return localSearch(name);
		}
		File returnFile = null;

		// local search
		IProject project = getProject();
		if (project != null) {
			for (int i = 0; i < paths.length; i++) {
				final IResource res = project.findMember(format(paths[i], name));
				if (res != null) {
					returnFile = res.getLocation().toFile();
					if (returnFile.equals(featureModelFile)) {
						returnFile = null;
					} else {
						break;
					}
				}
			}
		}

		// external search
		if (returnFile == null) {
			// if could not get current project or could not find file in current
			// project assume the name is the project name
			project = ResourcesPlugin.getWorkspace().getRoot().getProject(name);

			if (project.isAccessible()) {
				returnFile = project.getFile("model.xml").getLocation().toFile();
				if (returnFile.equals(featureModelFile)) {
					return null;
				}
			} else {
				Logger.logWarning(format("Project %s is not accessible.", name));
			}
		}

		if ((returnFile == null) || !returnFile.exists() || !returnFile.canRead()) {
			return null;
		}
		return returnFile;
	}

	private File getInterfaceModelFile(String name) {
		if (localSearch) {
			return localSearch(name);
		}
		File returnFile = null;
		final IProject project = getProject();
		if (project != null) {
			final IResource res = project.findMember(format("Interfaces/%s.velvet", name));
			if (res != null) {
				returnFile = res.getLocation().toFile();
			}
		}
		return returnFile;
	}

	private File localSearch(final String name) {
		final File searchDir = featureModelFile.getParentFile();
		if (searchDir != null) {
			final File[] files = searchDir.listFiles(new FilenameFilter() {

				@Override
				public boolean accept(File dir, String fileName) {
					final int index = fileName.lastIndexOf('.');
					return (index > 0) && fileName.substring(0, index).equals(name) && fileName.substring(index + 1).matches("xml|velvet");
				}
			});
			if ((files != null) && (files.length > 0)) {
				return files[0];
			}
		}
		return null;
	}

	/**
	 * Returns the eclipse project of the file with the textual representation of the feature model
	 *
	 * @return the project of the file or null if not known
	 */
	private IProject getProject() {
		if (featureModelFile == null) {
			return null;
		}

		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IPath filePath;
		try {
			filePath = Path.fromOSString(featureModelFile.getCanonicalPath());
			final IFile file = workspace.getRoot().getFileForLocation(filePath);
			if ((null == file) || !file.exists()) {
				return workspace.getRoot().getFile(filePath).getProject();
			}
			return file.getProject();
		} catch (final IOException e) {
			Logger.logError(e);
			return null;
		}
	}

	/**
	 * Initializes all variables.
	 */
	private void init() {
		atrributeConstraintNodes.clear();
		parentStack.clear();
		constraintNodeList.clear();
		usedVariables.clear();

		extFeatureModel.reset();
		// TODO Layout
//		extFeatureModel.getLayout().showHiddenFeatures(true);
//		extFeatureModel.getLayout().verticalLayout(false);
		if (getProject() != null) {
			modelMarkerHandler = new ModelMarkerHandler<IResource>(getProject().getFile(getFile().getName()));
			modelMarkerHandler.deleteAllModelMarkers();
		}

		extFeatureModelName = null;
		extFeatureModel.setInterface(false);

		// TODO MPL: Hack for local search
		localSearch = (featureModelFile != null) && (featureModelFile.getParentFile() != null) && featureModelFile.getParentFile().getName().equals("velvet");
	}

	private void parseAttribute(final Tree root, final IFeature parent) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		final String name = checkTree(nodeList.poll()).getText();
		final Tree valueNode = nodeList.poll();

		switch (valueNode.getType()) {
		case VelvetParser.FLOAT:
			break;
		case VelvetParser.INT:
			extFeatureModel.addAttribute(parent.getName(), name, Integer.parseInt(valueNode.getText()));
			break;
		case VelvetParser.BOOLEAN:
			extFeatureModel.addAttribute(parent.getName(), name, Boolean.parseBoolean(valueNode.getText()));
			break;
		case VelvetParser.STRING:
			final String valueNodeText = valueNode.getText();
			extFeatureModel.addAttribute(parent.getName(), name, valueNodeText.substring(1, valueNodeText.length() - 1));
			break;
		default:
			reportSyntaxError(valueNode);
		}
	}

	private void parseAttributeConstraints() throws UnsupportedModelException, RecognitionException {
		while (!atrributeConstraintNodes.isEmpty()) {
			final LinkedList<Tree> nodeList = getChildren(atrributeConstraintNodes.poll());

			final LinkedList<WeightedTerm> weightedTerms = new LinkedList<WeightedTerm>();
			RelationOperator relationOperator = null;
			boolean minus = false;
			int degree = 0;

			while (!nodeList.isEmpty()) {
				final Tree curNode = nodeList.poll();

				switch (curNode.getType()) {
				case VelvetParser.ID:
				case VelvetParser.IDPath:
					final String attributeName = curNode.getText();

					final Collection<FeatureAttribute<Integer>> attributes = extFeatureModel.getIntegerAttributes().getAttributes(attributeName);

					if (attributes == null) {
						throw new UnsupportedModelException(curNode.getLine() + ":" + curNode.getCharPositionInLine() + NO_SUCH_ATTRIBUTE_DEFINED_,
								curNode.getLine());
					}

					for (final FeatureAttribute<Integer> attr : attributes) {
						weightedTerms.add(createTerm(attr.getValue(), relationOperator != null, minus,
								new Reference(attr.getFeatureName(), ReferenceType.FEATURE, attributeName)));
					}

					break;
				// case VelvetParser.FLOAT:
				// break;
				case VelvetParser.INT:
					final int value = Integer.parseInt(curNode.getText());
					if ((relationOperator == null) ^ minus) {
						degree -= value;
					} else {
						degree += value;
					}
					break;
				case VelvetParser.PLUS:
					minus = false;
					break;
				case VelvetParser.MINUS:
					minus = true;
					break;
				case VelvetParser.ATTR_OP_EQUALS:
					relationOperator = RelationOperator.EQUAL;
					break;
				case VelvetParser.ATTR_OP_NOT_EQUALS:
					relationOperator = RelationOperator.NOT_EQUAL;
					break;
				case VelvetParser.ATTR_OP_GREATER:
					relationOperator = RelationOperator.GREATER;
					break;
				case VelvetParser.ATTR_OP_GREATER_EQ:
					relationOperator = RelationOperator.GREATER_EQUAL;
					break;
				case VelvetParser.ATTR_OP_LESS:
					relationOperator = RelationOperator.LESS;
					break;
				case VelvetParser.ATTR_OP_LESS_EQ:
					relationOperator = RelationOperator.LESS_EQUAL;
					break;
				default:
					reportSyntaxError(curNode);
				}
			}
			final Equation equation = new Equation(weightedTerms, relationOperator, degree);
			extFeatureModel.addAttributeConstraint(equation);
		}
	}

	private void parseConcept(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.ID:
				extFeatureModelName = checkTree(curNode).getText();

				final ExtendedFeature rootFeature = factory.createFeature(extFeatureModel, extFeatureModelName);
				rootFeature.getStructure().setAbstract(true);
				rootFeature.getStructure().setMandatory(true);

				extFeatureModel.addFeature(rootFeature);
				extFeatureModel.getStructure().setRoot(rootFeature.getStructure());
				parentStack.push(rootFeature);

				break;
			case VelvetParser.BASEEXT:
				parseInheritance(curNode);
				break;
			case VelvetParser.IMPORTINSTANCE:
				parseInstanceImport(curNode);
				break;
			case VelvetParser.IMPORTINTERFACE:
				parseInterfaceImport(curNode);
				break;
			case VelvetParser.DEF:
				parseDefinitions(curNode);
				break;
			default:
				reportSyntaxError(curNode);
			}
		}

		for (final ConstraintNode constraintNode : constraintNodeList) {
			final String nameError = checkNode(constraintNode.computedNode);
			if (nameError == null) {
				extFeatureModel.addConstraint(factory.createConstraint(extFeatureModel, constraintNode.computedNode));
			} else {
				reportWarning(constraintNode.rawNode, format("There is no feature with the name %s.", nameError));
			}
		}
	}

	private void parseConstraint(final Tree root, final IFeature parent) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.ID:
				// name = curNode.getText();
				break;
			case VelvetParser.CONSTR:
				Node newNode = parseConstraint_rec(curNode);
				newNode = new Implies(new Literal(parent.getName()), newNode);
				constraintNodeList.add(new ConstraintNode(newNode, curNode));
				break;
			case VelvetParser.ACONSTR:
				atrributeConstraintNodes.add(curNode);
				break;
			default:
				reportSyntaxError(curNode);
			}
		}
	}

	private Node parseConstraint_rec(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);
		final LinkedList<Node> nodes = new LinkedList<Node>();
		final LinkedList<Integer> operators = new LinkedList<Integer>();
		final LinkedList<Integer> unaryOp = new LinkedList<Integer>();
		Node n = null;

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.UNARYOP:
				unaryOp.push(curNode.getChild(0).getType());
				break;
			case VelvetParser.CONSTR:
				n = parseConstraint_rec(curNode);
				break;
			case VelvetParser.OPERAND:
				n = new Literal(curNode.getChild(0).getText());
				break;
			default:
				operators.add(curNode.getType());
			}

			if (n != null) {
				while (!unaryOp.isEmpty()) {
					switch (unaryOp.pop()) {
					case VelvetParser.OP_NOT:
						n = new Not(n);
					}
				}
				nodes.add(n);
				n = null;
			}
		}
		if (!operators.isEmpty()) {
			for (final int operator : binaryOperators) {
				final ListIterator<Node> nodesIt = nodes.listIterator();
				for (final ListIterator<Integer> opIt = operators.listIterator(); opIt.hasNext();) {
					final Node operand1 = nodesIt.next();
					if (opIt.next() == operator) {
						opIt.remove();
						nodesIt.remove();
						final Node operand2 = nodesIt.next();
						switch (operator) {
						case VelvetParser.OP_AND:
							nodesIt.set(new And(operand1, operand2));
							break;
						case VelvetParser.OP_OR:
							nodesIt.set(new Or(operand1, operand2));
							break;
						case VelvetParser.OP_XOR:
							nodesIt.set(new Choose(1, operand1, operand2));
							break;
						case VelvetParser.OP_IMPLIES:
							nodesIt.set(new Implies(operand1, operand2));
							break;
						case VelvetParser.OP_EQUIVALENT:
							nodesIt.set(new Equals(operand1, operand2));
							break;
						}
						nodesIt.previous();
					}
				}
			}
		}
		if (nodes.isEmpty()) {
			return null;
		}

		return nodes.getFirst();
	}

	private void parseDefinitions(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		final IFeature parentFeature = parentStack.pop();
		parentFeature.getStructure().setAnd();

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			// Feature
			case VelvetParser.FEATURE:
				parseFeature(curNode, parentFeature);
				break;
			// Feature-Group
			case VelvetParser.GROUP:
				parseFeatureGroup(curNode, parentFeature);
				break;
			// Constraint
			case VelvetParser.CONSTRAINT:
				parseConstraint(curNode, parentFeature);
				break;
			// Use
			case VelvetParser.USE:
				parseUse(curNode, parentFeature);
				break;
			// Attribute
			case VelvetParser.ATTR:
				parseAttribute(curNode, parentFeature);
				break;
			case VelvetParser.DESCRIPTION:
				parseDescription(curNode, parentFeature);
				break;
			case VelvetParser.EMPTY:
				break;
			default:
				reportSyntaxError(curNode);
			}
		}

	}

	private void parseDescription(Tree root, IFeature parent) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);
		final Tree valueNode = nodeList.poll();

		switch (valueNode.getType()) {
		case VelvetParser.STRING:
			final String valueNodeText = valueNode.getText();
			parent.getProperty().setDescription(valueNodeText.substring(1, valueNodeText.length() - 1).replace("\\\"", "\""));
			break;
		default:
			reportSyntaxError(valueNode);
		}
	}

	private void parseFeature(final Tree root, IFeature parent) throws RecognitionException {
		final LinkedList<Tree> childList = getChildren(root);
		final String featureName;
		if (extFeatureModel.isInterface()) {
			featureName = checkTree(childList.poll()).getText();
		} else {
			if (velvetImport || parent.getStructure().isRoot()) {
				featureName = checkTree(childList.poll()).getText();
			} else {
				featureName = parent.getName() + "." + checkTree(childList.poll()).getText();
			}
		}
		boolean isMandatory = false, isAbstract = false, moreDefinitions = false;

		Tree childNode = null;
		while (!childList.isEmpty() && !moreDefinitions) {
			childNode = childList.poll();

			switch (childNode.getType()) {
			case VelvetParser.MANDATORY:
				isMandatory = true;
				break;
			case VelvetParser.ABSTRACT:
				isAbstract = true;
				break;
			case VelvetParser.DEF:
				moreDefinitions = true;
				break;
			default:
				reportSyntaxError(childNode);
			}
		}

		final ExtendedFeature newFeature = addFeature(parent, featureName, isMandatory, isAbstract, false);
		if (moreDefinitions) {
			parentStack.push(newFeature);
			parseDefinitions(childNode);
		}
	}

	private void parseFeatureGroup(final Tree root, final IFeature parent) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.SOMEOF:
				parent.getStructure().setOr();
				break;
			case VelvetParser.ONEOF:
				parent.getStructure().setAlternative();
				break;
			case VelvetParser.FEATURE:
				parseFeature(curNode, parent);
				break;
			default:
				reportSyntaxError(curNode);
			}
		}
	}

	private void parseInheritance(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();
			final String parentModelName = checkTree(curNode).getText();

			final IFeatureModel fm = getExternalFeatureModel(curNode);
			if (fm == null) {
				return;
			}

			if (!extFeatureModel.addInheritance(parentModelName, parentModelName)) {
				reportWarning(curNode, THE_PARENT_MODEL + parentModelName + IS_ALREADY_USED_);
				return;
			}
			addExternalFeatures(fm, parentModelName, extFeatureModel.getStructure().getRoot(), ExtendedFeature.TYPE_INHERITED);
		}
	}

	private void addExternalFeatures(IFeatureModel sourceModel, String sourceModelName, IFeatureStructure targetParentFeature, int type) {
		if (sourceModel instanceof ExtendedFeatureModel) {
			for (final UsedModel usedModel : ((ExtendedFeatureModel) sourceModel).getExternalModels().values()) {
				extFeatureModel.addExternalModel(new UsedModel(usedModel, sourceModelName));
			}
		}

		final UsedModel usedModel = extFeatureModel.getExternalModel(sourceModelName);
		if (usedModel != null) {
			usedModel.setPrefix(targetParentFeature.getFeature().getName() + "." + sourceModelName);
		}

		final IFeatureStructure instanceRoot = sourceModel.getStructure().getRoot();
		final String connectorName = (targetParentFeature.isRoot() && targetParentFeature.getFeature().getName().equals(sourceModelName)) ? sourceModelName
			: targetParentFeature.getFeature().getName() + "." + sourceModelName;
		final ExtendedFeature connector = addFeature(targetParentFeature.getFeature(), connectorName, true, true, instanceRoot.isHidden());
		connector.setType(type);
		connector.setExternalModelName(sourceModelName);
		if (instanceRoot.isAlternative()) {
			connector.getStructure().setAlternative();
		} else if (instanceRoot.isOr()) {
			connector.getStructure().setOr();
		}

		copyChildnodes(extFeatureModel, connector.getStructure(), instanceRoot, sourceModelName, connectorName, type);

		for (final IConstraint constraint : sourceModel.getConstraints()) {
			final Node constraintNode = constraint.getNode();
			updateConstraintNode(constraintNode, connectorName, instanceRoot.getFeature().getName());
			final ExtendedConstraint newConstraint = factory.createConstraint(extFeatureModel, constraintNode);
			newConstraint.setType(type);
			newConstraint.setContainedFeatures();
			extFeatureModel.addConstraint(newConstraint);
		}
	}

	private void parseInterfaceImport(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree idNode = checkTree(nodeList.poll());
			final String interfaceName = idNode.getText();
			final Tree nameNode = checkTree(nodeList.poll());
			final String varName = nameNode.getText();

			if (checkInterfaceModelFile(idNode)) {
				if (!extFeatureModel.addInterface(interfaceName, varName)) {
					reportWarning(idNode, THE_VARIABLE_NAME + varName + IS_ALREADY_IN_USE_);
				}
			}
		}
	}

	private void parseInstanceImport(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree idNode = checkTree(nodeList.poll());
			final String interfaceName = idNode.getText();
			final Tree nameNode = checkTree(nodeList.poll());
			final String varName = nameNode.getText();

			if (checkExternalModelFile(idNode)) {
				if (!extFeatureModel.addInstance(interfaceName, varName)) {
					reportWarning(idNode, THE_VARIABLE_NAME + varName + IS_ALREADY_IN_USE_);
				}
			}
		}
	}

	private void parseModel(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);
		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();
			switch (curNode.getType()) {
			case VelvetParser.CONCEPT:
				parseConcept(curNode);
				break;
			case VelvetParser.CINTERFACE:
				extFeatureModel.setInterface(true);
				parseConcept(curNode);
				break;
			case VelvetParser.EOF:
				if (curNode.getTokenStartIndex() > -1) {
					break;
				}
			default:
				reportSyntaxError(curNode);
			}
		}
		final IFeatureModelFactory mappingModelFactory = FMFactoryManager.getDefaultFactory();
		final IFeatureModel mappingModel = mappingModelFactory.createFeatureModel();
		final IFeatureStructure rootFeature = mappingModelFactory.createFeature(mappingModel, "MPL").getStructure();
		rootFeature.setAnd();
		rootFeature.setAbstract(true);
		rootFeature.setMandatory(true);

		final LinkedList<String> possibleProjects = new LinkedList<String>();
		final IProject[] projects = ResourcesPlugin.getWorkspace().getRoot().getProjects();
		for (int i = 0; i < projects.length; i++) {
			final IProject project = projects[i];
			if (project.isAccessible()) {
				possibleProjects.add(project.getName());
			}
		}

		for (final Entry<String, UsedModel> parameter : extFeatureModel.getExternalModels().entrySet()) {
			if (parameter.getValue().getType() == ExtendedFeature.TYPE_INTERFACE) {
				final IFeatureStructure parameterFeature = mappingModelFactory.createFeature(mappingModel, parameter.getKey()).getStructure();
				parameterFeature.setOr();
				parameterFeature.setAbstract(true);
				parameterFeature.setMandatory(true);
				rootFeature.addChild(parameterFeature);

				for (final String projectName : possibleProjects) {
					final IFeatureStructure projectFeature =
						mappingModelFactory.createFeature(mappingModel, parameterFeature.getFeature().getName() + "." + projectName).getStructure();
					projectFeature.setAbstract(false);
					projectFeature.setMandatory(false);
					parameterFeature.addChild(projectFeature);
				}
			}
		}

		mappingModel.getStructure().setRoot(rootFeature);
		extFeatureModel.setMappingModel(mappingModel);

	}

	private void parseUse(Tree root, IFeature parent) throws RecognitionException {
		final LinkedList<Tree> childList = getChildren(root);
		final Tree useNameNode = checkTree(childList.poll());
		final String varName = useNameNode.getText();

		if (!usedVariables.add(varName)) {
			reportWarning(useNameNode, format("The Variable with the name %s was already used in this model.", varName));
			return;
		}

		final UsedModel usedModel = extFeatureModel.getExternalModel(varName);
		if (usedModel == null) {
			reportWarning(useNameNode, format("No variable with the name %s found.", varName));
			return;
		}

		switch (usedModel.getType()) {
		case ExtendedFeature.TYPE_INTERFACE:
			final IFeatureModel interfaceModel = getInterfaceFeatureModel(usedModel.getModelName(), useNameNode);
			if (interfaceModel == null) {
				return;
			}
			addExternalFeatures(interfaceModel, varName, parent.getStructure(), ExtendedFeature.TYPE_INTERFACE);
			break;
		case ExtendedFeature.TYPE_INSTANCE:
			final IFeatureModel instanceModel = getExternalFeatureModel(usedModel.getModelName(), useNameNode);
			if (instanceModel == null) {
				return;
			}
			addExternalFeatures(instanceModel, varName, parent.getStructure(), ExtendedFeature.TYPE_INSTANCE);
			break;
		default:
			reportWarning(useNameNode, format("The variable with the name %s is no interface or instance.", varName));
		}
	}

	private void reportWarning(Tree curNode, String message) {
		if (modelMarkerHandler != null) {
			modelMarkerHandler.createModelMarker(message, org.eclipse.core.resources.IMarker.SEVERITY_WARNING, curNode.getLine());
		}
		Logger.logWarning(message + " (at line " + curNode.getLine() + ((featureModelFile != null) ? IN_FILE + featureModelFile.getName() : "") + ": \""
			+ curNode.getText() + "\")");
	}

	private Tree checkTree(Tree root) throws RecognitionException {
		if (root instanceof CommonErrorNode) {
			throwException(((CommonErrorNode) root).trappedException, root);
		}
		return root;
	}

	private void reportSyntaxError(Tree curNode) throws RecognitionException {
		checkTree(curNode);
		final RecognitionException ex = new RecognitionException();
		ex.line = 1;
		ex.charPositionInLine = 1;
		throwException(ex, curNode);
	}

	private void throwException(RecognitionException e, Tree curNode) throws RecognitionException {
		if (modelMarkerHandler != null) {
			final String message = ILLEGAL_SYNTAX_IN_LINE + e.line + ":" + e.charPositionInLine + ". " + curNode.getText();
			modelMarkerHandler.createModelMarker(message, org.eclipse.core.resources.IMarker.SEVERITY_ERROR, e.line);
		}
		throw e;
	}
}
