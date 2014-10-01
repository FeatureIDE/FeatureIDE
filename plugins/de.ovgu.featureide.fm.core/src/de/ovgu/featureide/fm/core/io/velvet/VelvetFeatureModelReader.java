/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.io.velvet;

import static java.lang.String.format;

import java.io.File;
import java.io.FileNotFoundException;
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

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.ExtendedConstraint;
import de.ovgu.featureide.fm.core.ExtendedFeature;
import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.ExtendedFeatureModel.UsedModel;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.ModelMarkerHandler;
import de.ovgu.featureide.fm.core.constraint.Equation;
import de.ovgu.featureide.fm.core.constraint.FeatureAttribute;
import de.ovgu.featureide.fm.core.constraint.Reference;
import de.ovgu.featureide.fm.core.constraint.ReferenceType;
import de.ovgu.featureide.fm.core.constraint.RelationOperator;
import de.ovgu.featureide.fm.core.constraint.WeightedTerm;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.ModelIOFactory;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Parses a feature model in Velvet syntax.
 * 
 * @author Sebastian Krieter
 * @author Matthias Strauss
 */
public class VelvetFeatureModelReader extends AbstractFeatureModelReader {
	
	private static class ConstraintNode {
		private final Node computedNode;
		private final Tree rawNode;
		
		public ConstraintNode(Node computedNode, Tree rawNode) {
			this.computedNode = computedNode;
			this.rawNode = rawNode;
		}
	}

	private static final int[] binaryOperators = { 
		VelvetParser.OP_OR, VelvetParser.OP_AND, 
		VelvetParser.OP_XOR, VelvetParser.OP_IMPLIES,
		VelvetParser.OP_EQUIVALENT
	};
	private static final String[] paths = { 
		"%s.velvet", "%s.xml", "MPL/%s.velvet"
	};
	
	private final LinkedList<Tree> atrributeConstraintNodes = new LinkedList<Tree>();
	private final LinkedList<Feature> parentStack = new LinkedList<Feature>();
	private final LinkedList<ConstraintNode> constraintNodeList = new LinkedList<ConstraintNode>();
	private final HashSet<String> usedVariables = new HashSet<String>();
	
	private ModelMarkerHandler modelMarkerHandler;
	private ExtendedFeatureModel extFeatureModel;
	private String extFeatureModelName;
	private boolean cinterface, localSearch = false;
	
	/**
	 * Reads external model with the right FeatureModelReader.
	 * 
	 * @param file
	 *            file of feature model
	 * @return the feature model or null if error occurred
	 */
	private FeatureModel readExternalModelFile(File file) {
		final int modelType = ModelIOFactory.getTypeByFileName(file.getName());
		if (modelType != ModelIOFactory.TYPE_UNKNOWN) {
			final FeatureModel fm = ModelIOFactory.getNewFeatureModel(modelType);
			final AbstractFeatureModelReader reader = ModelIOFactory.getModelReader(fm, modelType);
			try {				
				reader.readFromFile(file);
				return fm;
			} catch (FileNotFoundException e) {
				FMCorePlugin.getDefault().logError(e);
			} catch (UnsupportedModelException e) {
				FMCorePlugin.getDefault().logError(e);
			}	
		}
		return null;
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

	private static void copyChildnodes(final ExtendedFeatureModel targetModel,
			final Feature targetParentNode, final Feature sourceParentNode,
			final String parentModelName, final String parentNodeName, final int type) {
		for (final Feature child : sourceParentNode.getChildren()) {
			final ExtendedFeature feature = new ExtendedFeature(targetModel, parentNodeName + "." + child.getName());
			feature.setMandatory(child.isMandatory());
			feature.setAbstract(child.isAbstract());
			feature.setHidden(child.isHidden());
			feature.setExternalModelName(parentModelName);

			feature.setAND(child.isAnd());
			feature.setMultiple(child.isMultiple());
			if (child.isOr()) {
				feature.setOr();
			}

			targetModel.addFeature(feature);
			targetParentNode.addChild(feature);
			feature.setType(type);

			if (child.hasChildren()) {
				copyChildnodes(targetModel, feature, child, parentModelName, parentNodeName, type);
			}
		}
	}

	private static WeightedTerm createTerm(final int weight, final boolean rightSide,
			final boolean minus, final Reference reference) {
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
			Literal literal = (Literal) curNode;
			if (literal.var.equals(rootName)) {
				literal.var = parentModelname;
			} else {
				literal.var = parentModelname + "." + literal.var.toString();
			}
		} else {
			for (Node child : curNode.getChildren()) {
				updateConstraintNode(child, parentModelname, rootName);
			}
		}
	}

	public VelvetFeatureModelReader(final FeatureModel featureModel) {
		extFeatureModel = (ExtendedFeatureModel) featureModel;
		setFeatureModel(extFeatureModel);
	}

	@Override
	protected synchronized void parseInputStream(final InputStream inputStream) throws UnsupportedModelException {
		ANTLRInputStream antlrInputStream = null;
		try {
			antlrInputStream = new ANTLRInputStream(inputStream);
		} catch (final IOException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		if (antlrInputStream == null) {
			throw new UnsupportedModelException("Syntax error!", 0);
		}
		final VelvetParser parser = new VelvetParser(new CommonTokenStream(new VelvetLexer(antlrInputStream)));
		Tree root = null;
		try {
			root = (Tree) parser.velvetModel().getTree();
		} catch (final RecognitionException e) {
			throw new UnsupportedModelException(e.getMessage(), e.line);
		}
		if (root == null) {
			throw new UnsupportedModelException("Error while reading model!", 0);
		}
		
		init();

		parseModel(root);
		parseAttributeConstraints();
		
		// Update the FeatureModel in Editor
		extFeatureModel.handleModelDataLoaded();
	}

	private ExtendedFeature addFeature(final Feature parent, final String featureName,
			final boolean isMandatory, final boolean isAbstract, final boolean isHidden) {
		final ExtendedFeature newFeature = new ExtendedFeature(extFeatureModel, featureName);
		newFeature.setMandatory(isMandatory);
		newFeature.setAbstract(isAbstract);
		newFeature.setHidden(isHidden);

		Feature orgFeature = extFeatureModel.getFeature(featureName);
		if (orgFeature != null && orgFeature instanceof ExtendedFeature) {
			return (ExtendedFeature) orgFeature;
		} else {
			extFeatureModel.addFeature(newFeature);
			parent.addChild(newFeature);
			return newFeature;
		}
	}

	private String checkNode(Node curNode) {
		if (curNode instanceof Literal) {
			Literal literal = (Literal) curNode;
			String varString = literal.var.toString();
			if (extFeatureModel.getFeature(varString) == null) {
				return literal.var.toString();
			}
		} else {
			for (Node child : curNode.getChildren()) {
				String childRet = checkNode(child);
				if (childRet != null) {
					return childRet;
				}
			}
		}
		return null;
	}
	
	private FeatureModel getExternalFeatureModel(Tree curNode) {
		final File modelFile = getExternalModelFile(curNode.getText());
		if (modelFile == null) {
			reportWarning(curNode, format("No model for %s could be found.", curNode.getText()));
			return null;
		}
		return readModel(modelFile, curNode);
	}
	
	private FeatureModel getExternalFeatureModel(String modelName, Tree curNode) {
		final File modelFile = getExternalModelFile(modelName);
		if (modelFile == null) {
			return null;
		}
		return readModel(modelFile, curNode);
	}
	
	private FeatureModel getInterfaceFeatureModel(String modelName, Tree curNode) {
		final File modelFile = getInterfaceModelFile(modelName);
		if (modelFile == null) {
			return null;
		}
		return readModel(modelFile, curNode);
	}
	
	private FeatureModel readModel(File modelFile, Tree curNode) {
		final FeatureModel fm = readExternalModelFile(modelFile);
		if (fm == null) {
			reportWarning(curNode, format("External model for %s could not be read.", curNode.getText()));
			return null;
		}
		return fm;
	}

	/**
	 * Search for the right File to include etc. The following search path is
	 * used:
	 * <ol>
	 * <li>./NAME.velvet</li>
	 * <li>./NAME.xml</li>
	 * <li>./MPL/NAME.velvet</li>
	 * <li>/NAME_AS_PROJECT/model.xml</li>
	 * </ol>
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
				FMCorePlugin.getDefault().logWarning(format("Project %s is not accessible.", name));
			}
		}
		
		if (returnFile == null || !returnFile.exists() || !returnFile.canRead()) {
			return null;
		}
		return returnFile;
	}
	
	private File getInterfaceModelFile(String name) {
		if (localSearch) {
			return localSearch(name);
		}
		File returnFile = null;
		IProject project = getProject();
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
			File[] files = searchDir.listFiles(new FilenameFilter() {
				@Override
				public boolean accept(File dir, String fileName) {
					int index = fileName.lastIndexOf('.');					
					return index > 0
						&& fileName.substring(0,index).equals(name)
						&& fileName.substring(index + 1).matches("xml|velvet");
				}
			});
			if (files != null && files.length > 0) {
				return files[0];
			}
		}
		return null;
	}

	/**
	 * Returns the eclipse project of the file with the textual representation
	 * of the feature model
	 * 
	 * @return the project of the file or null if not known
	 */
	private IProject getProject() {
		if (featureModelFile == null) {
			return null;
		}

		IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IPath filePath;
		try {
			filePath = Path.fromOSString(featureModelFile.getCanonicalPath());
			IFile file = workspace.getRoot().getFileForLocation(filePath);
			if (null == file || !file.exists()) {
				return workspace.getRoot().getFile(filePath).getProject();
			}
			return file.getProject();
		} catch (IOException e) {
			FMCorePlugin.getDefault().logError(e);
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
		extFeatureModel.getLayout().showHiddenFeatures(true);
		extFeatureModel.getLayout().verticalLayout(false);
		
		modelMarkerHandler = new ModelMarkerHandler(getProject().getFile(getFile().getName()));
		modelMarkerHandler.deleteAllModelMarkers();

		extFeatureModelName = null;
		cinterface = false;
		
		// TODO MPL: Hack for local search
		localSearch = featureModelFile != null
				&& featureModelFile.getParentFile() != null 
				&& featureModelFile.getParentFile().getName().equals("velvet");
	}

	private void parseAttribute(final Tree root, final Feature parent) {
		final LinkedList<Tree> nodeList = getChildren(root);

		final String name = nodeList.poll().getText();
		final Tree valueNode = nodeList.poll();

		switch (valueNode.getType()) {
		case VelvetParser.FLOAT:
			break;
		case VelvetParser.INT:
			this.extFeatureModel.addAttribute(parent.getName(), name,
					Integer.parseInt(valueNode.getText()));
			break;
		case VelvetParser.BOOLEAN:
			this.extFeatureModel.addAttribute(parent.getName(), name,
					Boolean.parseBoolean(valueNode.getText()));
			break;
		case VelvetParser.STRING:
			this.extFeatureModel.addAttribute(parent.getName(), name,
					valueNode.getText());
			break;
		default:
			reportSyntaxError(valueNode);
		}
	}

	private void parseAttributeConstraints() throws UnsupportedModelException {
		while (!this.atrributeConstraintNodes.isEmpty()) {
			final LinkedList<Tree> nodeList = getChildren(this.atrributeConstraintNodes.poll());

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

					final Collection<FeatureAttribute<Integer>> attributes = this.extFeatureModel
							.getIntegerAttributes().getAttributes(attributeName);

					if (attributes == null) {
						throw new UnsupportedModelException(curNode.getLine()
								+ ":" + curNode.getCharPositionInLine()
								+ " no such attribute defined.",
								curNode.getLine());
					}

					for (final FeatureAttribute<Integer> attr : attributes) {
						weightedTerms.add(createTerm(attr.getValue(),
								relationOperator != null, minus, 
								new Reference(attr.getFeatureName(), ReferenceType.FEATURE, attributeName)));
					}

					break;
				// case VelvetParser.FLOAT:
				// break;
				case VelvetParser.INT:
					final int value = Integer.parseInt(curNode.getText());
					if (relationOperator == null ^ minus) {
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

	private void parseConcept(final Tree root) {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.ID:
				extFeatureModelName = curNode.getText();

				final ExtendedFeature rootFeature = new ExtendedFeature(extFeatureModel, extFeatureModelName);
				rootFeature.setAbstract(true);
				rootFeature.setMandatory(true);

				extFeatureModel.addFeature(rootFeature);
				extFeatureModel.setRoot(rootFeature);
				parentStack.push(rootFeature);

				break;
			case VelvetParser.BASEEXT:
				parseInheritance(curNode);
				break;
			case VelvetParser.INST:
				parseInstanceImport(curNode);
				break;
			case VelvetParser.INTF:
				parseInterfaceImport(curNode);
				break;
			case VelvetParser.DEF:
				parseDefinitions(curNode);
				break;
			default:
				reportSyntaxError(curNode);
			}
		}
		
		for (ConstraintNode constraintNode : constraintNodeList) {
			String nameError = checkNode(constraintNode.computedNode);
			if (nameError == null) {
				extFeatureModel.addConstraint(new ExtendedConstraint(extFeatureModel, constraintNode.computedNode));
			} else {
				reportWarning(constraintNode.rawNode, format("There is no feature with the name %s.", nameError));
			}
		}
	}

	private void parseConstraint(final Tree root, final Feature parent) {
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
				this.atrributeConstraintNodes.add(curNode);
				break;
			default:
				reportSyntaxError(curNode);
			}
		}
	}

	private Node parseConstraint_rec(final Tree root) {
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

	private void parseDefinitions(final Tree root) {
		final LinkedList<Tree> nodeList = getChildren(root);

		final Feature parentFeature = parentStack.pop();
		parentFeature.setAnd();

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			// Feature
			case VelvetParser.FEAT:
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
			case VelvetParser.USES:
				parseUse(curNode, parentFeature);
				break;
			// Attribute
			case VelvetParser.ATTR:
				parseAttribute(curNode, parentFeature);
				break;
			case VelvetParser.EMPTY:
				break;
			default:
				reportSyntaxError(curNode);
			}
		}

	}

	private void parseFeature(final Tree root, Feature parent) {
		final LinkedList<Tree> childList = getChildren(root);
		final String featureName;
		if (cinterface) {
			featureName = childList.poll().getText();
		} else {
			if (parent.isRoot()) {
				featureName = childList.poll().getText();
			} else {
				featureName = parent.getName() + "." + childList.poll().getText();
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

	private void parseFeatureGroup(final Tree root, final Feature parent) {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.SOMEOF:
				parent.setOr();
				break;
			case VelvetParser.ONEOF:
				parent.setAlternative();
				break;
			case VelvetParser.FEAT:
				parseFeature(curNode, parent);
				break;
			default:
				reportSyntaxError(curNode);
			}
		}
	}

	private void parseInheritance(final Tree root) {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();
			final String parentModelName = curNode.getText();

			final FeatureModel fm = getExternalFeatureModel(curNode);
			if (fm == null) {
				return;
			}
			
			if (!extFeatureModel.addInheritance(parentModelName, parentModelName)) {
				reportWarning(curNode, "The parent model " + parentModelName + " is already used.");
				return;
			}
			addExternalFeatures(fm, parentModelName, extFeatureModel.getRoot(), ExtendedFeature.TYPE_INHERITED);
		}
	}
	
	private void addExternalFeatures(FeatureModel sourceModel, String sourceModelName, Feature targetParentFeature, int type) {
		if (sourceModel instanceof ExtendedFeatureModel) {
			for (UsedModel usedModel : ((ExtendedFeatureModel) sourceModel).getExternalModels().values()) {
				extFeatureModel.addExternalModel(new UsedModel(usedModel, sourceModelName));
			}
		}
		
		UsedModel usedModel = extFeatureModel.getExternalModel(sourceModelName);
		if (usedModel != null) {
			usedModel.setPrefix(targetParentFeature.getName() + "." + sourceModelName);
		}
		
		final Feature instanceRoot = sourceModel.getRoot();
		final String connectorName = (targetParentFeature.isRoot() && targetParentFeature.getName().equals(sourceModelName)) 
				? sourceModelName 
				: targetParentFeature.getName() + "." + sourceModelName;
		final ExtendedFeature connector = addFeature(targetParentFeature, connectorName, true, true, instanceRoot.isHidden());
		connector.setType(type);
		connector.setExternalModelName(sourceModelName);
		if (instanceRoot.isAlternative()) {
			connector.setAlternative();
		} else if (instanceRoot.isOr()) {
			connector.setOr();
		}

		copyChildnodes(extFeatureModel, connector, instanceRoot, sourceModelName, connectorName, type);
		
		for (final Constraint constraint : sourceModel.getConstraints()) {
			Node constraintNode = constraint.getNode();
			updateConstraintNode(constraintNode, connectorName, instanceRoot.getName());
			ExtendedConstraint newConstraint = new ExtendedConstraint(extFeatureModel, constraintNode);
			newConstraint.setType(type);
			newConstraint.setContainedFeatures();
			extFeatureModel.addConstraint(newConstraint);
		}
	}
	
	private void parseInterfaceImport(final Tree root) {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree idNode = nodeList.poll();
			final String interfaceName = idNode.getText();
			final Tree nameNode = nodeList.poll();
			final String varName = nameNode.getText();
			
			if (checkInterfaceModelFile(idNode)) {
				if (!extFeatureModel.addInterface(interfaceName, varName)) {
					reportWarning(idNode, "The variable name " + varName + " is already in use.");
				}
			}
		}
	}
	
	private void parseInstanceImport(final Tree root) {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree idNode = nodeList.poll();
			final String interfaceName = idNode.getText();
			final Tree nameNode = nodeList.poll();
			final String varName = nameNode.getText();
			
			if (checkExternalModelFile(idNode)) {
				if (!extFeatureModel.addInstance(interfaceName, varName)) {
					reportWarning(idNode, "The variable name " + varName + " is already in use.");
				}
			}
		}
	}

	private void parseModel(final Tree root) {
		final LinkedList<Tree> nodeList = getChildren(root);
		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();
			switch (curNode.getType()) {
			case VelvetParser.CONCEPT:
				parseConcept(curNode);
				break;
			case VelvetParser.CINTERFACE:
				cinterface = true;
				parseConcept(curNode);
				break;
			case VelvetParser.EOF:
				// TODO MPL: check if a model was created?
				break;
			default:
				reportSyntaxError(curNode);
			}
		}
		FeatureModel mappingModel = new FeatureModel();
		Feature rootFeature = new Feature(mappingModel, "MPL");
		rootFeature.setAnd();
		rootFeature.setAbstract(true);
		rootFeature.setMandatory(true);
		
		LinkedList<String> possibleProjects = new LinkedList<String>();
		IProject[] projects = ResourcesPlugin.getWorkspace().getRoot().getProjects();
		for (int i = 0; i < projects.length; i++) {
			IProject project = projects[i];
			if (project.isAccessible()) {
				possibleProjects.add(project.getName());
			}
		}
		
		for (Entry<String, UsedModel> parameter : extFeatureModel.getExternalModels().entrySet()) {
			if (parameter.getValue().getType() == ExtendedFeature.TYPE_INTERFACE) {
				Feature parameterFeature = new Feature(mappingModel, parameter.getKey());
				parameterFeature.setOr();
				parameterFeature.setAbstract(true);
				parameterFeature.setMandatory(true);
				rootFeature.addChild(parameterFeature);
				
				for (String projectName : possibleProjects) {
					Feature projectFeature = new Feature(mappingModel, parameterFeature.getName() + "." + projectName);
					projectFeature.setAbstract(false);
					projectFeature.setMandatory(false);
					parameterFeature.addChild(projectFeature);
				}
			}
		}
		
		mappingModel.setRoot(rootFeature);
		extFeatureModel.setMappingModel(mappingModel);
		
	}

	private void parseUse(Tree root, Feature parent) {
		final LinkedList<Tree> childList = getChildren(root);
		final Tree useNameNode = childList.poll();
		final String varName = useNameNode.getText();
		
		if (!usedVariables.add(varName)) {
			reportWarning(useNameNode, format("The Variable with the name %s was already used in this model.", varName));
			return;
		}
		
		UsedModel usedModel = extFeatureModel.getExternalModel(varName);
		if (usedModel == null) {
			reportWarning(useNameNode, format("No variable with the name %s found.", varName));
			return;
		}
		
		switch (usedModel.getType()) {
		case ExtendedFeature.TYPE_INTERFACE:
			final FeatureModel interfaceModel = getInterfaceFeatureModel(usedModel.getModelName(), useNameNode);
			if (interfaceModel == null) {
				return;
			}
			addExternalFeatures(interfaceModel, varName, parent, ExtendedFeature.TYPE_INTERFACE);
			break;
		case ExtendedFeature.TYPE_INSTANCE:
			final FeatureModel instanceModel = getExternalFeatureModel(usedModel.getModelName(), useNameNode);
			if (instanceModel == null) {
				return;
			}
			addExternalFeatures(instanceModel, varName, parent, ExtendedFeature.TYPE_INSTANCE);
			break;
		default:
			reportWarning(useNameNode, format("The variable with the name %s is no interface or instance.", varName));
		}
	}
	
	private void reportSyntaxError(Tree curNode) {
		String message = "Illegal statement \""+ curNode.getText() + "\"";
		modelMarkerHandler.createModelMarker(message, org.eclipse.core.resources.IMarker.SEVERITY_ERROR, curNode.getLine());
		FMCorePlugin.getDefault().logError(new UnsupportedModelException(
			message + " at line " + curNode.getLine() + ((featureModelFile != null)?" in file " + featureModelFile.getName():""), curNode.getLine()));
	}
	
	private void reportWarning(Tree curNode, String message) {
		modelMarkerHandler.createModelMarker(message, org.eclipse.core.resources.IMarker.SEVERITY_WARNING, curNode.getLine());
		FMCorePlugin.getDefault().logWarning(message + " (at line "+ curNode.getLine() + ((featureModelFile != null)?" in file " + featureModelFile.getName():"") + ": \"" + curNode.getText() + "\")");		
	}
}
