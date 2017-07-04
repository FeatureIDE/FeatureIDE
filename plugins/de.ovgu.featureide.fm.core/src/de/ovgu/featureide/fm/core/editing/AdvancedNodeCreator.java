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
package de.ovgu.featureide.fm.core.editing;

import java.util.ArrayList;
import java.util.List;
import java.util.ListIterator;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.prop4j.Literal.FeatureAttribute;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

/**
 * Removes features from a model while retaining dependencies of all other feature.
 * 
 * @author Sebastian Krieter
 */
public class AdvancedNodeCreator implements LongRunningMethod<Node> {

	public static enum CNFType {
		None, Compact, Regular
	}

	public static enum ModelType {
		All, OnlyConstraints, OnlyStructure
	}

	public static Node createCNF(IFeatureModel featureModel) {
		AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel);
		nodeCreator.setCnfType(CNFType.Compact);
		return nodeCreator.createNodes();
	}

	public static Node createRegularCNF(IFeatureModel featureModel) {
		AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel);
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(false);
		return nodeCreator.createNodes();
	}

	public static Node createNodes(IFeatureModel featureModel) {
		return new AdvancedNodeCreator(featureModel).createNodes();
	}

	private CNFType cnfType = CNFType.None;

	private ModelType modelType = ModelType.All;

	private boolean includeBooleanValues = true;

	private boolean useOldNames = true;

	private boolean optionalRoot = false;

	private IFeatureModel featureModel = null;

	public AdvancedNodeCreator() {
	}

	public AdvancedNodeCreator(IFeatureModel featureModel) {
		setFeatureModel(featureModel);
	}

	public AdvancedNodeCreator(IFeatureModel featureModel, CNFType cnfType, ModelType modelType, boolean includeBooleanValues) {
		this.cnfType = cnfType;
		this.modelType = modelType;
		this.includeBooleanValues = includeBooleanValues;
		setFeatureModel(featureModel);
	}

//	private Literal getVariable(IFeature feature, boolean positive) {
//		final String oldName = useOldNames ? feature.getFeatureModel().getRenamingsManager().getOldName(feature.getName()) : feature.getName();
//		return new Literal(oldName, positive);
//	}

	private Literal getVariable(IFeature feature, boolean positive, FeatureAttribute a) {
		final String oldName = useOldNames ? feature.getFeatureModel().getRenamingsManager().getOldName(feature.getName()) : feature.getName();
		return new Literal(oldName, positive, a);
	}

	private And createConstraintNodes() {
		final List<Node> clauses = new ArrayList<>(featureModel.getConstraints().size());
		boolean compact = true;
		switch (cnfType) {
		case None:
			for (IConstraint constraint : featureModel.getConstraints()) {
				clauses.add(constraint.getNode().clone());
			}
			break;
		case Regular:
			compact = false;
		case Compact:
		default:
			for (IConstraint constraint : featureModel.getConstraints()) {
				final Node cnfNode = Node.buildCNF(constraint.getNode());
				//				final Node cnfNode = constraint.getNode().toCNF();
				if (cnfNode instanceof And) {
					for (Node andChild : cnfNode.getChildren()) {
						clauses.add((compact || (andChild instanceof Or)) ? andChild : new Or(andChild));
					}
				} else {
					clauses.add((compact || (cnfNode instanceof Or)) ? cnfNode : new Or(cnfNode));
				}
			}
			break;
		}
		return new And(clauses.toArray(new Node[0]));
	}

	public Node createNodes() {
		return createNodes(new NullMonitor());
	}

	public Node createNodes(IMonitor monitor) {
		if (featureModel == null) {
			final Or emptyNode = includeBooleanValues ? new Or(new Literal(NodeCreator.varTrue), new Literal(NodeCreator.varFalse, false)) : new Or();
			switch (cnfType) {
			case Regular:
				return new And(emptyNode);
			case None:
			case Compact:
			default:
				return emptyNode;
			}
		}

		monitor.setRemainingWork(10);
		return new And(createFormula(monitor.subTask(1)));
	}

	private Node[] createFormula(IMonitor monitor) {
		monitor.setTaskName("Creating Formula");
		monitor.setRemainingWork(2);
		final Node[] andChildren1;
		final Node[] andChildren2;

		switch (modelType) {
		case All:
			andChildren1 = createStructuralNodes().getChildren();
			andChildren2 = createConstraintNodes().getChildren();
			break;
		case OnlyConstraints:
			andChildren1 = new Node[0];
			andChildren2 = createConstraintNodes().getChildren();
			break;
		case OnlyStructure:
			andChildren1 = createStructuralNodes().getChildren();
			andChildren2 = new Node[0];
			break;
		default:
			andChildren1 = new Node[0];
			andChildren2 = new Node[0];
			break;
		}
		monitor.step();

		final int length = andChildren1.length + andChildren2.length;
		final Node[] nodeArray;
		if (includeBooleanValues) {
			nodeArray = new Node[length + 2];

			switch (cnfType) {
			case Regular:
				nodeArray[length] = new Or(new Literal[] { new Literal(NodeCreator.varTrue) });
				nodeArray[length + 1] = new Or(new Literal[] { new Literal(NodeCreator.varFalse, false) });
				break;
			case None:
			case Compact:
			default:
				nodeArray[length] = new Literal(NodeCreator.varTrue);
				nodeArray[length + 1] = new Literal(NodeCreator.varFalse, false);
				break;
			}
		} else {
			nodeArray = new Node[length];
		}
		System.arraycopy(andChildren1, 0, nodeArray, 0, andChildren1.length);
		System.arraycopy(andChildren2, 0, nodeArray, andChildren1.length, andChildren2.length);
		monitor.step();

		return nodeArray;
	}

	private And createStructuralNodes() {
		final IFeature root = FeatureUtils.getRoot(featureModel);
		if (root != null) {
			final List<Node> clauses = new ArrayList<>(featureModel.getNumberOfFeatures());

			if (!optionalRoot) {
				switch (cnfType) {
				case Regular:
					clauses.add(new Or(getVariable(root, true, FeatureAttribute.ROOT)));
					break;
				case None:
				case Compact:
				default:
					clauses.add(getVariable(root, true, FeatureAttribute.ROOT));
					break;
				}
			}

			final Iterable<IFeature> features = featureModel.getFeatures();
			for (IFeature feature : features) {
				for (IFeatureStructure child : feature.getStructure().getChildren()) {
					clauses.add(new Or(getVariable(feature, true, FeatureAttribute.PARENT), getVariable(child.getFeature(), false, FeatureAttribute.CHILD)));
				}

				if (feature.getStructure().hasChildren()) {
					if (feature.getStructure().isAnd()) {
						for (IFeatureStructure child : feature.getStructure().getChildren()) {
							if (child.isMandatory()) {
								clauses.add(new Or(getVariable(child.getFeature(), true, FeatureAttribute.CHILD), getVariable(feature, false, FeatureAttribute.PARENT)));
							}
						}
					} else if (feature.getStructure().isOr()) {
						final Literal[] orLiterals = new Literal[feature.getStructure().getChildren().size() + 1];
						int i = 0;
						for (IFeatureStructure child : feature.getStructure().getChildren()) {
							orLiterals[i++] = getVariable(child.getFeature(), true, FeatureAttribute.CHILD);
						}
						orLiterals[i] = getVariable(feature, false, FeatureAttribute.PARENT);
						clauses.add(new Or(orLiterals));
					} else if (feature.getStructure().isAlternative()) {
						final Literal[] alternativeLiterals = new Literal[feature.getStructure().getChildrenCount() + 1];
						int i = 0;
						for (IFeatureStructure child : feature.getStructure().getChildren()) {
							alternativeLiterals[i++] = getVariable(child.getFeature(), true, FeatureAttribute.CHILD);
						}
						alternativeLiterals[i] = getVariable(feature, false, FeatureAttribute.PARENT);
						clauses.add(new Or(alternativeLiterals));

						for (ListIterator<IFeatureStructure> it1 = feature.getStructure().getChildren().listIterator(); it1.hasNext();) {
							final IFeatureStructure fs = it1.next();
							for (ListIterator<IFeatureStructure> it2 = feature.getStructure().getChildren().listIterator(it1.nextIndex()); it2.hasNext();) {
								clauses.add(new Or(getVariable(fs.getFeature(), false, FeatureAttribute.CHILD), getVariable(((IFeatureStructure) it2.next()).getFeature(), false, FeatureAttribute.CHILD)));
							}
						}
					}
				}
			}

			return new And(clauses.toArray(new Node[0]));
		}
		return new And(new Node[0]);
	}

	@Override
	public Node execute(IMonitor monitor) throws Exception {
		return createNodes(monitor);
	}

	public CNFType getCnfType() {
		return cnfType;
	}

	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	public ModelType getModelType() {
		return modelType;
	}

	/**
	 * {@link #includeBooleanValues}
	 * 
	 * @return the currently set value
	 */
	public boolean includeBooleanValues() {
		return includeBooleanValues;
	}

	public void setCnfType(CNFType cnfType) {
		this.cnfType = cnfType;
	}

	public void setUseOldNames(boolean useOldNames) {
		this.useOldNames = useOldNames;
	}

	public void setFeatureModel(IFeatureModel featureModel) {
		this.featureModel = featureModel;
	}

	/**
	 * {@link #includeBooleanValues}
	 * 
	 * @param includeBooleanValues the value to set
	 */
	public void setIncludeBooleanValues(boolean includeBooleanValues) {
		this.includeBooleanValues = includeBooleanValues;
	}

	public void setModelType(ModelType modelType) {
		this.modelType = modelType;
	}

	public boolean optionalRoot() {
		return optionalRoot;
	}

	public void setOptionalRoot(boolean optionalRoot) {
		this.optionalRoot = optionalRoot;
	}

}
