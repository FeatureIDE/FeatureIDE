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

import static de.ovgu.featureide.fm.core.localization.StringTable.IN_FILE;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_SUCH_ATTRIBUTE_DEFINED_;
import static java.lang.String.format;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.nio.file.Path;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.ListIterator;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.CommonErrorNode;
import org.antlr.runtime.tree.Tree;
import org.prop4j.And;
import org.prop4j.Choose;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.ExtendedConstraint;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.constraint.Equation;
import de.ovgu.featureide.fm.core.constraint.FeatureAttribute;
import de.ovgu.featureide.fm.core.constraint.Reference;
import de.ovgu.featureide.fm.core.constraint.ReferenceType;
import de.ovgu.featureide.fm.core.constraint.RelationOperator;
import de.ovgu.featureide.fm.core.constraint.WeightedTerm;
import de.ovgu.featureide.fm.core.io.AFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Reads / Writes feature models in the Velvet format.
 *
 * @author Sebastian Krieter
 * @author Matthias Strauss
 * @author Reimar Schroeter
 */
public class SimpleVelvetFeatureModelFormat extends AFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + SimpleVelvetFeatureModelFormat.class.getSimpleName();

	protected Path featureModelFile;
	protected ProblemList problemList;

	private static final String[] SYMBOLS = { "!", "&&", "||", "->", "<->", ", ", "choose", "atleast", "atmost" };
	private static final String NEWLINE = System.getProperty("line.separator", "\n");
	private final StringBuilder sb = new StringBuilder();

	public SimpleVelvetFeatureModelFormat() {
		super();
	}

	public SimpleVelvetFeatureModelFormat(AFeatureModelFormat oldFormat) {
		super(oldFormat);
	}

	@Override
	public boolean supportsRead() {
		return true;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String write(IFeatureModel object) {
		if (object instanceof ExtendedFeatureModel) {
			extFeatureModel = (ExtendedFeatureModel) object;
		}
		final IFeatureStructure root = object.getStructure().getRoot();
		sb.delete(0, sb.length());

		sb.append("concept ");

		sb.append(root.getFeature().getName());
		sb.append(" {");
		sb.append(NEWLINE);

		if (extFeatureModel != null) {
			for (final IFeatureStructure child : root.getChildren()) {
				writeNewDefined(child, 1);
			}

			for (final IConstraint constraint : object.getConstraints()) {
				if (((ExtendedConstraint) constraint).getType() == ExtendedFeature.TYPE_INTERN) {
					sb.append("\tconstraint ");
					sb.append(constraint.getNode().toString(SYMBOLS));
					sb.append(";");
					sb.append(NEWLINE);
				}
			}
		} else {
			writeFeatureGroup(root, 1);

			for (final IConstraint constraint : object.getConstraints()) {
				sb.append("\tconstraint ");
				sb.append(constraint.getNode().toString(SYMBOLS));
				sb.append(";");
				sb.append(NEWLINE);
			}
		}

		sb.append("}");

		return sb.toString();
	}

	private void writeFeatureGroup(IFeatureStructure root, int depth) {
		if (root.isAnd()) {
			for (final IFeatureStructure feature : root.getChildren()) {
				writeFeature(feature, depth + 1);
			}
		} else if (root.isOr()) {
			writeTab(depth + 1);
			sb.append("someOf {");
			sb.append(NEWLINE);
			for (final IFeatureStructure feature : root.getChildren()) {
				writeFeature(feature, depth + 2);
			}
			writeTab(depth + 1);
			sb.append("}");
			sb.append(NEWLINE);
		} else if (root.isAlternative()) {
			writeTab(depth + 1);
			sb.append("oneOf {");
			sb.append(NEWLINE);
			for (final IFeatureStructure f : root.getChildren()) {
				writeFeature(f, depth + 2);
			}
			writeTab(depth + 1);
			sb.append("}");
			sb.append(NEWLINE);
		}
	}

	private void writeFeature(IFeatureStructure feature, int depth) {
		writeTab(depth);
		if (feature.isAbstract()) {
			sb.append("abstract ");
		}
		if (feature.isMandatory() && ((feature.getParent() == null) || feature.getParent().isAnd())) {
			sb.append("mandatory ");
		}
		sb.append("feature ");
		sb.append(feature.getFeature().getName());
		final String description = feature.getFeature().getProperty().getDescription();
		final boolean hasDescription = (description != null) && !description.isEmpty();

		if ((feature.getChildrenCount() == 0) && !hasDescription) {
			sb.append(";");
		} else {
			sb.append(" {");
			sb.append(NEWLINE);
			if (hasDescription) {
				writeTab(depth + 1);
				sb.append("description \"");
				sb.append(description.replace("\"", "\\\""));
				sb.append("\";");
				sb.append(NEWLINE);
			}

			writeFeatureGroup(feature, depth);

			writeTab(depth);
			sb.append("}");
		}
		sb.append(NEWLINE);
	}

	private void writeNewDefined(IFeatureStructure child2, int depth) {
		writeFeature(child2, 1);
		for (final IFeatureStructure child : child2.getChildren()) {
			writeNewDefined(child, depth);
		}
	}

	private void writeTab(int times) {
		for (int i = 0; i < times; i++) {
			sb.append('\t');
		}
	}

	@Override
	public ProblemList read(IFeatureModel object, CharSequence source) {
		problemList = new ProblemList();
		factory = ExtendedFeatureModelFactory.getInstance();
		extFeatureModel = (ExtendedFeatureModel) object;
		if (extFeatureModel != null) {
			featureModelFile = extFeatureModel.getSourceFile();
		}

		final ByteArrayInputStream inputstr = new ByteArrayInputStream(source.toString().getBytes(Charset.availableCharsets().get("UTF-8")));
		try {
			parseInputStream(inputstr);
		} catch (final UnsupportedModelException e) {
			problemList.add(new Problem(e, e.lineNumber));
		}
		return problemList;
	}

	private static class ConstraintNode {

		private final Node computedNode;
		private final Tree rawNode;

		public ConstraintNode(Node computedNode, Tree rawNode) {
			this.computedNode = computedNode;
			this.rawNode = rawNode;
		}
	}

	private static final int[] binaryOperators =
		{ VelvetParser.OP_OR, VelvetParser.OP_AND, VelvetParser.OP_XOR, VelvetParser.OP_IMPLIES, VelvetParser.OP_EQUIVALENT };

	private final LinkedList<Tree> atrributeConstraintNodes = new LinkedList<Tree>();
	private final LinkedList<IFeature> parentStack = new LinkedList<IFeature>();
	private final LinkedList<ConstraintNode> constraintNodeList = new LinkedList<ConstraintNode>();
	private final HashSet<String> usedVariables = new HashSet<String>();

	private final boolean velvetImport = false;

	private ExtendedFeatureModel extFeatureModel;
	private String extFeatureModelName;

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
			final UnsupportedModelException unsupportedModelException = new UnsupportedModelException(e.getMessage(), e.line);
			unsupportedModelException.addSuppressed(e);
			throw unsupportedModelException;
		}
	}

	private ExtendedFeature addFeature(final IFeature parent, final String featureName, final boolean isMandatory, final boolean isAbstract,
			final boolean isHidden) {
		final ExtendedFeature newFeature = (ExtendedFeature) factory.createFeature(extFeatureModel, featureName);
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

	/**
	 * Initializes all variables.
	 */
	private void init() {
		atrributeConstraintNodes.clear();
		parentStack.clear();
		constraintNodeList.clear();
		usedVariables.clear();

		extFeatureModel.reset();

		extFeatureModelName = null;
		extFeatureModel.setInterface(false);
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

				final ExtendedFeature rootFeature = (ExtendedFeature) factory.createFeature(extFeatureModel, extFeatureModelName);
				rootFeature.getStructure().setAbstract(true);
				rootFeature.getStructure().setMandatory(true);

				extFeatureModel.addFeature(rootFeature);
				extFeatureModel.getStructure().setRoot(rootFeature.getStructure());
				parentStack.push(rootFeature);

				break;
			case VelvetParser.BASEEXT:
				reportWarning(curNode, "Inheritance are not supported.");
				break;
			case VelvetParser.IMPORTINSTANCE:
				reportWarning(curNode, "Instances are not supported.");
				break;
			case VelvetParser.IMPORTINTERFACE:
				reportWarning(curNode, "Interfaces are not supported.");
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

		if ((validator != null) && !validator.isValidFeatureName(featureName)) {
			problemList.add(new Problem(featureName + " is not a valid feature name", root.getLine(), de.ovgu.featureide.fm.core.io.Problem.Severity.ERROR));
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
	}

	private void parseUse(Tree root, IFeature parent) throws RecognitionException {
		reportWarning(root, "USE is not supported.");
	}

	private void reportWarning(Tree curNode, String message) {
		Logger.logWarning(message + " (at line " + curNode.getLine() + ((featureModelFile != null) ? IN_FILE + featureModelFile.getFileName() : "") + ": \""
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
		throw e;
	}

	@Override
	public String getSuffix() {
		return "velvet";
	}

	@Override
	public SimpleVelvetFeatureModelFormat getInstance() {
		return new SimpleVelvetFeatureModelFormat(this);
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public boolean initExtension() {
		if (super.initExtension()) {
			FMFactoryManager.getFactoryWorkspace().assignID(SimpleVelvetFeatureModelFormat.ID, ExtendedFeatureModelFactory.ID);
		}
		return false;
	}

	@Override
	public String getName() {
		return "Simple Velevet";
	}

}
