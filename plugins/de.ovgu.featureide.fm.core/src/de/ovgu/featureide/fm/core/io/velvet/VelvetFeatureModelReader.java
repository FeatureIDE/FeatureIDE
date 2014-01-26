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
import java.io.IOException;
import java.io.InputStream;
import java.util.Collection;
import java.util.LinkedList;
import java.util.ListIterator;

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
import de.ovgu.featureide.fm.core.io.FileLoader;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Parses a feature model in Velvet syntax.
 * 
 * @author Sebastian Krieter
 * @author Matthias Strauss
 */
public class VelvetFeatureModelReader
	extends
		AbstractFeatureModelReader {

	private enum FeatureInheritanceModes {
		INHERITANCE,
		INSTANCE,
		INTERFACE;
	}

	protected ExtendedFeatureModel extFeatureModel;
	private final LinkedList<Feature> parentStack = new LinkedList<Feature>();;
	private boolean copiedShadowModel = false;

	private final LinkedList<Tree> atrributeConstraintNodes = new LinkedList<Tree>();
	private static final int[] binaryOperators = {VelvetParser.OP_OR, VelvetParser.OP_AND, VelvetParser.OP_XOR,
		VelvetParser.OP_IMPLIES, VelvetParser.OP_EQUIVALENT};

	public VelvetFeatureModelReader(final FeatureModel featureModel) {
		this.extFeatureModel = (ExtendedFeatureModel) featureModel;
		setFeatureModel(this.extFeatureModel);
	}

	private Feature addFeature(final ExtendedFeatureModel model,
			final Feature parent,
			final String featureName,
			final boolean isMandatory,
			final boolean isAbstract,
			final boolean isHidden) {
		final Feature newFeature = new Feature(model, featureName);
		newFeature.setMandatory(isMandatory);
		newFeature.setAbstract(isAbstract);
		newFeature.setHidden(isHidden);

		model.addFeature(newFeature);
		parent.addChild(newFeature);

		return newFeature;
	}

	private void copyChildnodes(final ExtendedFeatureModel model,
			final Feature parentNode,
			final LinkedList<Feature> children,
			final String parent,
			final FeatureInheritanceModes mode) {
		for (final Feature child : children) {
			final Feature feature =
				addFeature(model, parentNode, child.getName(), child.isMandatory(), child.isAbstract(),
					child.isHidden());
			// save imported feature into mapping to store imported status
			feature.setAND(child.isAnd());
			feature.setMultiple(child.isMultiple());
			if (child.isOr()) {
				feature.setOr();
			}
			switch (mode) {
				case INHERITANCE:
					model.setFeatureInherited(feature, parent);
					break;
				case INSTANCE:
					model.setFeaturefromInstance(feature, parent);
					break;
				case INTERFACE:
					model.setFeatureInterface(feature, parent);
					break;
			}

			if (child.hasChildren()) {
				copyChildnodes(model, feature, child.getChildren(), parent, mode);
			}
		}
	}

	private void copyModel(final ExtendedFeatureModel model, final FeatureModel parent, final String parentModelName) {
		final Feature root = parent.getRoot();

		copyChildnodes(model, model.getRoot(), root.getChildren(), parentModelName, FeatureInheritanceModes.INHERITANCE);
		for (final Constraint constraint : parent.getConstraints()) {
			model.addConstraint(constraint);
		}
	}

	private void copyShadowModel() {
		copyChildnodes(this.extFeatureModel, this.extFeatureModel.getRoot(), this.extFeatureModel.getShadowModel()
			.getRoot().getChildren(), "", FeatureInheritanceModes.INTERFACE);
	}

	private WeightedTerm createTerm(final int weight,
			final boolean rightSide,
			final boolean minus,
			final Reference reference) {
		boolean positive = weight >= 0;
		if (rightSide ^ minus) {
			positive = !positive;
		}
		return new WeightedTerm(Math.abs(weight), positive, reference);
	}

	private LinkedList<Tree> getChildren(final Tree root) {
		final LinkedList<Tree> children = new LinkedList<Tree>();

		final int childCount = root.getChildCount();
		for (int i = 0; i < childCount; i++) {
			children.add(root.getChild(i));
		}
		return children;
	}

	/**
	 * Returns the eclipse project of the file with the textual representation
	 * of the feature model
	 * 
	 * @return the project of the file or null if not known
	 */
	protected IProject getProject() {
		if (featureModelFile == null)
			return null;

		IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IPath filePath = Path.fromOSString(featureModelFile.getAbsolutePath());
		IFile file = workspace.getRoot().getFileForLocation(filePath);
		if (file == null)
			return null;

		return file.getProject();
	}

	/**
	 * TODO @Matthias create documentation
	 * 
	 * @param fm
	 * @param name
	 * @param instance
	 */
	private void insertInstance(final FeatureModel instance, final String instancename, final Feature parent) {
		final Feature instanceRoot = instance.getRoot();

		final Feature connector =
			addFeature(this.extFeatureModel.getShadowModel(), parent, instancename, false,
				instanceRoot.isAbstract(), instanceRoot.isHidden());
		this.extFeatureModel.setFeaturefromInstance(connector, instancename);
		if (instanceRoot.isAlternative()) {
			connector.setAlternative();
		}

		copyChildnodes(this.extFeatureModel.getShadowModel(), connector, instanceRoot.getChildren(), instancename,
			FeatureInheritanceModes.INSTANCE);
		for (final Constraint constraint : instance.getConstraints()) {
			this.extFeatureModel.getShadowModel().addConstraint(constraint);
		}
	}

	private void parseAttribute(final Tree root, final Feature parent) {
		// TODO adjust to shadowmodel
		final LinkedList<Tree> nodeList = getChildren(root);

		final String name = nodeList.poll().getText();
		final Tree valueNode = nodeList.poll();

		switch (valueNode.getType()) {
			case VelvetParser.FLOAT:
				break;
			case VelvetParser.INT:
				this.extFeatureModel.addAttribute(parent.getName(), name, Integer.parseInt(valueNode.getText()));
				break;
			case VelvetParser.BOOLEAN:
				this.extFeatureModel.addAttribute(parent.getName(), name, Boolean.parseBoolean(valueNode.getText()));
				break;
			case VelvetParser.STRING:
				this.extFeatureModel.addAttribute(parent.getName(), name, valueNode.getText());
				break;
		}
	}

	private void parseAttributeConstraints()
		throws UnsupportedModelException {
		// TODO adjust to shadow model
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

						final Collection<FeatureAttribute<Integer>> attributes =
							this.extFeatureModel.getIntegerAttributes().getAttributes(attributeName);

						if (attributes == null) {
							throw new UnsupportedModelException(curNode.getLine()
								+ ":"
								+ curNode.getCharPositionInLine()
								+ " no such attribute defined.", curNode.getLine());
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
			final Equation equation = new Equation(weightedTerms, relationOperator, degree);
			// FMCorePlugin.getDefault().logInfo(equation.toString());
			this.extFeatureModel.addAttributeConstraint(equation);
		}
	}

	private void parseConcept(final Tree root) {
		final LinkedList<Tree> nodeList = getChildren(root);
		final String tmpName = "tmp";
		final Feature rootFeature = new Feature(this.extFeatureModel, tmpName);
		rootFeature.setAbstract(true);
		rootFeature.setMandatory(true);

		this.extFeatureModel.addFeature(rootFeature);
		this.extFeatureModel.setRoot(rootFeature);
		this.parentStack.push(rootFeature);

		String name = null;
		// boolean refines = false;
		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
				case VelvetParser.ID:
					name = curNode.getText();
					break;
				case VelvetParser.REFINES:
					// refines = true;
					break;
				case VelvetParser.BASEEXT:
					this.extFeatureModel.createShadowModel();
					parseInheritance(curNode);
					break;
				case VelvetParser.BASEPARAM:
					parseParam(curNode);
					break;
				case VelvetParser.IMPLEMENT:
					parseImplements(curNode);
					break;
				case VelvetParser.DEF:
					if (null == this.extFeatureModel.implementsInterface()
						&& null != this.extFeatureModel.getShadowModel()
						&& !this.copiedShadowModel) {
						copyShadowModel();
						this.copiedShadowModel = true;
					}
					parseDefinitions(curNode);
					break;
				default:
					FMCorePlugin.getDefault().logError(
						new UnsupportedModelException(format("Illegal marker in concept header \"%s\"",
							curNode.getText()), 0));
			}
			
			// if model contained no definitions we need to copy the shadow model
			// because the section were this is done usuallly was skipped
			if (null == this.extFeatureModel.implementsInterface() &&
				null != this.extFeatureModel.getShadowModel() &&
				!this.copiedShadowModel) {
				copyShadowModel();
				this.copiedShadowModel = true;
			}
		}
		
		rootFeature.setName(name);
		this.extFeatureModel.renameFeature(tmpName, name);
		this.extFeatureModel.performRenamings();
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
					this.extFeatureModel.addConstraint(new Constraint(this.extFeatureModel,
						parseConstraint_rec(curNode)));
					break;
				case VelvetParser.ACONSTR:
					this.atrributeConstraintNodes.add(curNode);
					break;
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

		final Feature parentFeature = this.parentStack.pop();
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
				// Instance
				case VelvetParser.INSTANCE:
					parseInstance(curNode, parentFeature);
					break;
				// Attribute
				case VelvetParser.ATTR:
					parseAttribute(curNode, parentFeature);
					break;
			}
		}

	}

	private void parseFeature(final Tree root, Feature parent) {
		final LinkedList<Tree> childList = getChildren(root);
		final String featureName = childList.poll().getText();
		boolean isMandatory = false, isAbstract = false, moreDefinitions = false;

		for (final Feature feat : parent.getChildren()) {
			if (feat.getName().equals(featureName)) {
				// TODO @Matthias handle overwrite
				break;
			}
		}

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

		ExtendedFeatureModel writeModel;
		if (null == this.extFeatureModel.implementsInterface()) {
			// we parsed no interface. Therefore we can copy shadow model to the
			// original
			if (null == this.extFeatureModel.implementsInterface()
					&& null != extFeatureModel.getShadowModel()
					&& !this.copiedShadowModel){
				copyShadowModel();
				copiedShadowModel = true;
			}
			
			writeModel = this.extFeatureModel;
		} else {
			writeModel = this.extFeatureModel.getShadowModel();
			// FIXME UGLY UGLY UGLY hack.
			// fix me as soon and as good as possible
			/* Explanation:
			 * If a feature shall be added to a Model implementing an interface it shall be added to the shadow model.
			 * because the implementing model is not supposed to contain own features, but it could be useful to add
			 * features in it, to provide compatibility with the interface.
			 * 
			 * This method is called with a parent parameter which points to a feature in the original (interface implementing)
			 * model. Therefore we need to change the parent, if we're writing to the shadow model.
			 * 
			 * This approach could lead to errors if nested features are introduced into the shadow model this way.
			 */
			if (parent.equals(extFeatureModel.getRoot())) {
				parent = writeModel.getFeature(parent.getName());
				if (null == parent) {
					parent = writeModel.getRoot();
				}
			}
		}

		final Feature newFeature = addFeature(writeModel, parent, featureName, isMandatory, isAbstract, false);
		if (moreDefinitions) {
			this.parentStack.push(newFeature);
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
			}
		}
	}

	/**
	 * @param curNode
	 */
	private void parseImplements(final Tree root) {
		final String interfaceName = root.getChild(0).getText();
		this.extFeatureModel.setInterface(interfaceName);
		final ExtendedFeatureModel interf = new ExtendedFeatureModel();
		final VelvetFeatureModelReader interfaceReader = new VelvetFeatureModelReader(interf);

		final IProject parent = getProject();
		final IResource res = parent.findMember(format("Interfaces/%s.velvet", interfaceName));
		final File file = res.getLocation().toFile();
		System.err.println(file);

		try {
			interfaceReader.readFromFile(file);
			// copy interface into model
			copyChildnodes(this.extFeatureModel, this.extFeatureModel.getRoot(), interf.getRoot().getChildren(),
				interfaceName, FeatureInheritanceModes.INTERFACE);
		} catch ( final FileNotFoundException e ) {
			FMCorePlugin.getDefault().logError(e);
		} catch ( final UnsupportedModelException e ) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	private void parseInheritance(final Tree root) {
		// TODO maybe add a search path for imports.
		// it can only be inherited from model.xml's of other projects in the
		// same workspace and only if the modelname corresponds to the project
		// name
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();
			final String parentModelName = curNode.getText();

			final ExtendedFeatureModel shadow = this.extFeatureModel.getShadowModel();

			shadow.addParent(parentModelName);

			final IProject parent = ResourcesPlugin.getWorkspace().getRoot().getProject(parentModelName);

			if (!parent.exists()) {
				FMCorePlugin.getDefault().logWarning(format("Project %s is missing.", parentModelName));
				return;
			}

			final FeatureModel fm = FileLoader.loadFeatureModel(parent);
			copyModel(shadow, fm, parentModelName);
		}
	}

	@Override
	protected synchronized void parseInputStream(final InputStream inputStream)
		throws UnsupportedModelException {
		ANTLRInputStream antlrInputStream = null;
		try {
			antlrInputStream = new ANTLRInputStream(inputStream);
		} catch ( final IOException e ) {
			FMCorePlugin.getDefault().logError(e);
		}
		if (antlrInputStream != null) {
			final VelvetParser parser = new VelvetParser(new CommonTokenStream(new VelvetLexer(antlrInputStream)));
			Tree root = null;
			try {
				root = (Tree) parser.velvetModel().getTree();
			} catch ( final RecognitionException e ) {
				throw new UnsupportedModelException(e.getMessage(), e.line);
			}

			if (root != null) {
				this.extFeatureModel.reset();
				this.copiedShadowModel = false;
				
				parseModel(root);
				parseAttributeConstraints();

				final ExtendedFeatureModelAnalyzer analyzer = new ExtendedFeatureModelAnalyzer(this.extFeatureModel);
				FMCorePlugin.getDefault().logInfo("Velvet-Featuremodel imported");

				try {
					FMCorePlugin.getDefault().logInfo(analyzer.isValid() ? "valid" : "invalid");
				} catch ( final TimeoutException e ) {
					FMCorePlugin.getDefault().logError(e);
				}
				// Update the FeatureModel in Editor
				this.extFeatureModel.handleModelDataLoaded();
			}
		}
	}

	private void parseInstance(final Tree root, final Feature parentFeature) {
		final LinkedList<Tree> nodeList = getChildren(root);

		final String name = nodeList.poll().getText();
		final String var = nodeList.poll().getText();

		// TODO remove assumption that name == projectname
		// this.extFeatureModel.addInstance(parentModelName);

		final IProject parent = ResourcesPlugin.getWorkspace().getRoot().getProject(name);

		if (!parent.exists()) {
			FMCorePlugin.getDefault().logWarning(format("Project %s is missing.", name));
			return;
		}

		final FeatureModel fm = FileLoader.loadFeatureModel(parent);
		insertInstance(fm, var, parentFeature);
	}

	private void parseInstanceHeader(final Tree root) {
		final LinkedList<Tree> nodeList = getChildren(root);
		final String model = nodeList.poll().getText();
		final String name = nodeList.poll().getText();

		this.extFeatureModel.addInstanceMapping(name, model);
	}

	private void parseModel(final Tree root)
		throws UnsupportedModelException {
		this.extFeatureModel.getLayout().showHiddenFeatures(true);
		this.extFeatureModel.getLayout().verticalLayout(false);

		final LinkedList<Tree> nodeList = getChildren(root);
		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
				case VelvetParser.IMP:
					break;
				case VelvetParser.INSTANCEDEF:
					parseInstanceHeader(curNode);
				case VelvetParser.CONCEPT:
					parseConcept(curNode);
					break;
				case VelvetParser.CINTERFACE:
					parseConcept(curNode);
					break;
				case VelvetParser.EOF:
					// TODO @Matthias check if a model was created?
					break;
				default:
					FMCorePlugin
						.getDefault()
						.logError(
							new UnsupportedModelException(
								"Model contains invalid tokens in before beginning of concept or interface definition. (Line Number in velvet not available)",
								0));
					break;
			}
		}
	}

	private void parseParam(final Tree root) {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			final String interfaceClazz = curNode.getText();
			final String interfaceVar = nodeList.poll().getText();

			if (!this.extFeatureModel.addParameter(interfaceClazz, interfaceVar)) {
				// TODO @Matthias log an error
			}
		}
	}
}
