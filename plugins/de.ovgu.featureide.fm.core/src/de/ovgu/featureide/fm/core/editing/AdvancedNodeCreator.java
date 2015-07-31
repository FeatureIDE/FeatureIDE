/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.Collection;
import java.util.List;
import java.util.ListIterator;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.remove.FeatureRemover;
import de.ovgu.featureide.fm.core.filter.AbstractFeatureFilter;
import de.ovgu.featureide.fm.core.filter.HiddenFeatureFilter;
import de.ovgu.featureide.fm.core.filter.base.Filter;
import de.ovgu.featureide.fm.core.filter.base.IFilter;
import de.ovgu.featureide.fm.core.job.LongRunningJob;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

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

	public static Node createCNF(FeatureModel featureModel) {
		AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel);
		nodeCreator.setCnfType(CNFType.Compact);
		return nodeCreator.createNodes();
	}

	public static Node createCNFWithoutAbstract(FeatureModel featureModel) {
		AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel);
		nodeCreator.setExcludedFeatures(new AbstractFeatureFilter());
		nodeCreator.setCnfType(CNFType.Compact);
		return nodeCreator.createNodes();
	}

	public static Node createCNFWithoutHidden(FeatureModel featureModel) {
		AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel);
		nodeCreator.setExcludedFeatures(new HiddenFeatureFilter());
		nodeCreator.setCnfType(CNFType.Compact);
		return nodeCreator.createNodes();
	}

	public static Node createNodes(FeatureModel featureModel) {
		return new AdvancedNodeCreator(featureModel).createNodes();
	}

	public static Node createNodesWithoutAbstract(FeatureModel featureModel) {
		AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel);
		nodeCreator.setExcludedFeatures(new AbstractFeatureFilter());
		return nodeCreator.createNodes();
	}

	public static Node createNodesWithoutHidden(FeatureModel featureModel) {
		AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel);
		nodeCreator.setExcludedFeatures(new HiddenFeatureFilter());
		return nodeCreator.createNodes();
	}

	private static Literal getVariable(Feature feature, boolean positive) {
		return new Literal(feature.getFeatureModel().getRenamingsManager().getOldName(feature.getName()), positive);
	}

	private CNFType cnfType = CNFType.None;

	private ModelType modelType = ModelType.All;

	private FeatureModel featureModel = null;

	private Collection<String> excludedFeatureNames = null;

	public AdvancedNodeCreator(FeatureModel featureModel) {
		this.featureModel = featureModel;
	}

	public Node createNodes() {
		if (featureModel == null) {
			return null;
		}

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

		final int length = andChildren1.length + andChildren2.length;
		final Node[] nodeArray = new Node[length + 2];

		System.arraycopy(andChildren1, 0, nodeArray, 0, andChildren1.length);
		System.arraycopy(andChildren2, 0, nodeArray, andChildren1.length, andChildren2.length);

		switch (cnfType) {
		case Regular:
			nodeArray[length] = new Or(new Node[] { new Literal(NodeCreator.varTrue) });
			nodeArray[length + 1] = new Or(new Node[] { new Literal(NodeCreator.varFalse, false) });
			break;
		case None:
		case Compact:
		default:
			nodeArray[length] = new Literal(NodeCreator.varTrue);
			nodeArray[length + 1] = new Literal(NodeCreator.varFalse, false);
			break;
		}

		if (excludedFeatureNames != null && !excludedFeatureNames.isEmpty()) {
			return LongRunningJob.runMethod(new FeatureRemover(new And(nodeArray), excludedFeatureNames));
		} else {
			return new And(nodeArray);
		}
	}

	@Override
	public Node execute(WorkMonitor monitor) throws Exception {
		return createNodes();
	}

	public CNFType getCnfType() {
		return cnfType;
	}

	public Collection<String> getExcludedFeatureNames() {
		return excludedFeatureNames;
	}

	public FeatureModel getFeatureModel() {
		return featureModel;
	}

	public ModelType getModelType() {
		return modelType;
	}

	public void setCnfType(CNFType cnfType) {
		this.cnfType = cnfType;
	}

	public void setExcludedFeatureNames(Collection<String> excludedFeatureNames) {
		this.excludedFeatureNames = excludedFeatureNames;
	}

	public void setExcludedFeatures(Collection<Feature> excludedFeatures) {
		this.excludedFeatureNames = Filter.toString(excludedFeatures);
	}

	public void setExcludedFeatures(IFilter<Feature> featureFilter) {
		this.excludedFeatureNames = Filter.toString(Filter.filter(featureModel.getFeatures(), featureFilter));
	}

	public void setFeatureModel(FeatureModel featureModel) {
		this.featureModel = featureModel;
	}

	public void setModelType(ModelType modelType) {
		this.modelType = modelType;
	}

	private And createConstraintNodes() {
		final List<Node> clauses = new ArrayList<>(featureModel.getConstraints().size());
		switch (cnfType) {
		case None:
			for (Constraint constraint : featureModel.getConstraints()) {
				clauses.add(constraint.getNode().clone());
			}
		case Regular:
			for (Constraint constraint : featureModel.getConstraints()) {
				final Node cnfNode = constraint.getNode().clone().toCNF();
				if (cnfNode instanceof And) {
					for (Node andChild : cnfNode.getChildren()) {
						if (andChild instanceof Or) {
							clauses.add(new Or(andChild.getChildren()));
						} else {
							clauses.add(new Or((Literal) andChild));
						}
					}
				} else if (cnfNode instanceof Or) {
					clauses.add(new Or(cnfNode.getChildren()));
				} else {
					clauses.add(new Or((Literal) cnfNode));
				}
			}
		case Compact:
		default:
			for (Constraint constraint : featureModel.getConstraints()) {
				final Node cnfNode = constraint.getNode().clone().toCNF();
				if (cnfNode instanceof And) {
					for (Node andChild : cnfNode.getChildren()) {
						if (andChild instanceof Or) {
							clauses.add(new Or(andChild.getChildren()));
						} else {
							clauses.add(andChild);
						}
					}
				} else if (cnfNode instanceof Or) {
					clauses.add(new Or(cnfNode.getChildren()));
				} else {
					clauses.add(cnfNode);
				}
			}
			break;
		}
		return new And(clauses.toArray(new Node[0]));
	}

	private And createStructuralNodes() {
		final Feature root = featureModel.getRoot();
		if (root != null) {
			final List<Node> clauses = new ArrayList<>(featureModel.getNumberOfFeatures());

			switch (cnfType) {
			case Regular:
				clauses.add(new Or(getVariable(root, true)));
				break;
			case None:
			case Compact:
			default:
				clauses.add(getVariable(root, true));
				break;
			}

			final Collection<Feature> features = featureModel.getFeatures();
			for (Feature feature : features) {
				for (Feature child : feature.getChildren()) {
					clauses.add(new Or(getVariable(feature, true), getVariable(child, false)));
				}

				if (feature.isAnd()) {
					for (Feature child : feature.getChildren()) {
						if (child.isMandatory()) {
							clauses.add(new Or(getVariable(child, true), getVariable(feature, false)));
						}
					}
				} else if (feature.isOr()) {
					final Literal[] orLiterals = new Literal[feature.getChildrenCount() + 1];
					int i = 0;
					for (Feature child : feature.getChildren()) {
						orLiterals[i++] = getVariable(child, true);
					}
					orLiterals[i] = getVariable(feature, false);
					clauses.add(new Or(orLiterals));
				} else if (feature.isAlternative()) {
					final Literal[] alternativeLiterals = new Literal[feature.getChildrenCount() + 1];
					int i = 0;
					for (Feature child : feature.getChildren()) {
						alternativeLiterals[i++] = getVariable(child, true);
					}
					alternativeLiterals[i] = getVariable(feature, false);
					clauses.add(new Or(alternativeLiterals));

					for (ListIterator<Feature> it1 = feature.getChildren().listIterator(); it1.hasNext();) {
						final Feature feature1 = (Feature) it1.next();
						for (ListIterator<Feature> it2 = feature.getChildren().listIterator(it1.nextIndex()); it2.hasNext();) {
							clauses.add(new Or(getVariable(feature1, false), getVariable((Feature) it2.next(), false)));
						}

					}
				}
			}

			return new And(clauses.toArray(new Node[0]));
		}
		return new And(new Node[0]);
	}

}
