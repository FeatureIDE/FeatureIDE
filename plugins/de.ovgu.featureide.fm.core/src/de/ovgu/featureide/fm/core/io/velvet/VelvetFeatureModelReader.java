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

import java.io.IOException;
import java.io.InputStream;
import java.util.Collection;
import java.util.LinkedList;
import java.util.ListIterator;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.Tree;
import org.prop4j.And;
import org.prop4j.Choose;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.constraint.Equation;
import de.ovgu.featureide.fm.core.constraint.FeatureAttribute;
import de.ovgu.featureide.fm.core.constraint.Reference;
import de.ovgu.featureide.fm.core.constraint.ReferenceType;
import de.ovgu.featureide.fm.core.constraint.RelationOperator;
import de.ovgu.featureide.fm.core.constraint.WeightedTerm;
import de.ovgu.featureide.fm.core.constraint.analysis.ExtendedFeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Parses a feature model in Velvet syntax.
 * 
 * @author Sebastian Krieter
 */
public class VelvetFeatureModelReader extends AbstractFeatureModelReader {
	
	protected ExtendedFeatureModel extFeatureModel;

	public VelvetFeatureModelReader(FeatureModel featureModel) {
		extFeatureModel = (ExtendedFeatureModel) featureModel;
		setFeatureModel(extFeatureModel);
	}

	private final LinkedList<Feature> parentStack = new LinkedList<Feature>();
	private final LinkedList<Tree> atrributeConstraintNodes = new LinkedList<Tree>();

	private LinkedList<Tree> getChildren(Tree root) {
		LinkedList<Tree> children = new LinkedList<Tree>();

		int childCount = root.getChildCount();
		for (int i = 0; i < childCount; i++) {
			children.add(root.getChild(i));
		}
		return children;
	}

	private void parseModel(Tree root) {
		extFeatureModel.getLayout().showHiddenFeatures(true);
		extFeatureModel.getLayout().verticalLayout(false);

		LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.IMP:
				break;
			case VelvetParser.CONCEPT:
				parseConcept(curNode);
				break;
			}
		}
	}

	private void parseConcept(Tree root) {
		LinkedList<Tree> nodeList = getChildren(root);

		String name = null;
		// boolean refines = false;

		while (!nodeList.isEmpty()) {
			Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.ID:
				name = curNode.getText();
				break;
			case VelvetParser.REFINES:
				// refines = true;
				break;
			case VelvetParser.BASEEXT:
				break;
			case VelvetParser.DEF:
				Feature rootFeatrue = new Feature(extFeatureModel, name);
				extFeatureModel.addFeature(rootFeatrue);
				extFeatureModel.setRoot(rootFeatrue);
				parentStack.push(rootFeatrue);
				parseDefinitions(curNode);
				break;
			}
		}
	}

	private void parseDefinitions(Tree root) {
		LinkedList<Tree> nodeList = getChildren(root);

		Feature parentFeature = parentStack.pop();
		parentFeature.setAnd();

		while (!nodeList.isEmpty()) {
			Tree curNode = nodeList.poll();

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
			// Instance
			case VelvetParser.INSTANCE:
				break;
			// Attribute
			case VelvetParser.ATTR:
				parseAttribute(curNode, parentFeature);
				break;
			}
		}

	}

	private void parseFeatureGroup(Tree root, Feature parent) {
		LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			Tree curNode = nodeList.poll();

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
			}
		}
	}

	private void parseFeature(Tree root, Feature parent) {
		LinkedList<Tree> childList = getChildren(root);
		String featureName = childList.poll().getText();
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
			}
		}

		Feature newFeature = addFeature(parent, featureName, isMandatory, isAbstract, false);
		if (moreDefinitions) {
			parentStack.push(newFeature);
			parseDefinitions(childNode);
		}
	}

	private void parseConstraint(Tree root, Feature parent) {
		LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.ID:
				// name = curNode.getText();
				break;
			case VelvetParser.CONSTR:
				extFeatureModel.addConstraint(
						new Constraint(extFeatureModel, parseConstraint_rec(curNode)));
				break;
			case VelvetParser.ACONSTR:
				atrributeConstraintNodes.add(curNode);
				break;
			}
		}
	}

	private static final int[] binaryOperators = { VelvetParser.OP_OR,
			VelvetParser.OP_AND, VelvetParser.OP_XOR, VelvetParser.OP_IMPLIES,
			VelvetParser.OP_EQUIVALENT };

	private Node parseConstraint_rec(Tree root) {
		LinkedList<Tree> nodeList = getChildren(root);

		LinkedList<Node> nodes = new LinkedList<Node>();
		LinkedList<Integer> operators = new LinkedList<Integer>();
		LinkedList<Integer> unaryOp = new LinkedList<Integer>();
		Node n = null;

		while (!nodeList.isEmpty()) {
			Tree curNode = nodeList.poll();

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
			for (int i = 0; i < binaryOperators.length; i++) {
				ListIterator<Node> nodesIt = nodes.listIterator();
				int operator = binaryOperators[i];
				for (ListIterator<Integer> opIt = operators.listIterator(); opIt
						.hasNext();) {
					Node operand1 = nodesIt.next();
					if (opIt.next() == operator) {
						opIt.remove();
						nodesIt.remove();
						Node operand2 = nodesIt.next();
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
		if (nodes.isEmpty())
			return null;

		return nodes.getFirst();
	}
	
	private void parseAttribute(Tree root, Feature parent) {
		LinkedList<Tree> nodeList = getChildren(root);

		String name = nodeList.poll().getText();
		Tree valueNode = nodeList.poll();

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
			extFeatureModel.addAttribute(parent.getName(), name, valueNode.getText());
			break;
		}
	}
	
	private void parseAttributeConstraints() throws UnsupportedModelException {
		while (!atrributeConstraintNodes.isEmpty()) {
			LinkedList<Tree> nodeList = getChildren(atrributeConstraintNodes.poll());

			LinkedList<WeightedTerm> weightedTerms = new LinkedList<WeightedTerm>();
			RelationOperator relationOperator = null;
			boolean minus = false;
			int degree = 0;
			
			while (!nodeList.isEmpty()) {
				Tree curNode = nodeList.poll();
				
				switch (curNode.getType()) {
				case VelvetParser.ID:
				case VelvetParser.IDPath:
					String attributeName = curNode.getText();
					
					Collection<FeatureAttribute<Integer>> attributes = extFeatureModel.getIntegerAttributes().getAttributes(attributeName);
					
					if (attributes == null) {
						throw new UnsupportedModelException(
							curNode.getLine() + ":" + curNode.getCharPositionInLine() + 
							" no such attribute defined.", 
							curNode.getLine());
					}
					
					for (FeatureAttribute<Integer> attr : attributes) {
						weightedTerms.add(
							createTerm(
								attr.getValue(), 
								relationOperator != null,  minus,
								new Reference(attr.getFeatureName(), ReferenceType.FEATURE, attributeName)));
					}
					
					break;
//				case VelvetParser.FLOAT:
//					break;
				case VelvetParser.INT:
					int value = Integer.parseInt(curNode.getText());
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
				}
			}
			Equation equation = new Equation(weightedTerms, relationOperator, degree);
//			FMCorePlugin.getDefault().logInfo(equation.toString());
			extFeatureModel.addAttributeConstraint(equation);
		}
	}
	
	private WeightedTerm createTerm(int weight, boolean rightSide, boolean minus, Reference reference) {
		boolean positive = weight >= 0;
		if (rightSide ^ minus) {
			positive = !positive;
		}
		return new WeightedTerm(Math.abs(weight), positive, reference);
	}

	private Feature addFeature(Feature parent, String featureName,
			boolean isMandatory, boolean isAbstract, boolean isHidden) {
		Feature newFeature = new Feature(extFeatureModel, featureName);
		newFeature.setMandatory(isMandatory);
		newFeature.setAbstract(isAbstract);
		newFeature.setHidden(isHidden);

		extFeatureModel.addFeature(newFeature);
		parent.addChild(newFeature);

		return newFeature;
	}

	@Override
	protected synchronized void parseInputStream(InputStream inputStream)
			throws UnsupportedModelException {
		ANTLRInputStream antlrInputStream = null;
		try {
			antlrInputStream = new ANTLRInputStream(inputStream);
		} catch (IOException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		if (antlrInputStream != null) {
			VelvetParser parser = new VelvetParser(new CommonTokenStream(
					new VelvetLexer(antlrInputStream)));
			Tree root = null;
			try {
				root = (Tree) parser.velvetModel().getTree();
			} catch (RecognitionException e) {
				throw new UnsupportedModelException(e.getMessage(), e.line);
			}

			if (root != null) {
				extFeatureModel.reset();
				parseModel(root);
				parseAttributeConstraints();
				
				ExtendedFeatureModelAnalyzer analyzer = new ExtendedFeatureModelAnalyzer(extFeatureModel);
				FMCorePlugin.getDefault().logInfo("Velvet-Featuremodel imported");
				
				try {
					FMCorePlugin.getDefault().logInfo(analyzer.isValid() ? "valid" : "invalid");
				} catch (TimeoutException e) {
					FMCorePlugin.getDefault().logError(e);
				}
				// Update the FeatureModel in Editor
				extFeatureModel.handleModelDataLoaded();
			}
		}
	}
}