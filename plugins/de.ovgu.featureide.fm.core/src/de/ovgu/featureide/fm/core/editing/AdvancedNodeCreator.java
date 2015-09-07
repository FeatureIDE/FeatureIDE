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
import java.util.LinkedList;
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
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
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
		AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel, new AbstractFeatureFilter());
		nodeCreator.setCnfType(CNFType.Compact);
		return nodeCreator.createNodes();
	}

	public static Node createCNFWithoutHidden(FeatureModel featureModel) {
		AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel, new HiddenFeatureFilter());
		nodeCreator.setCnfType(CNFType.Compact);
		return nodeCreator.createNodes();
	}

	public static Node createNodes(FeatureModel featureModel) {
		return new AdvancedNodeCreator(featureModel).createNodes();
	}

	public static Node createNodes(FeatureModel featureModel, Collection<String> excludedFeatureNames, CNFType cnfType, ModelType modelType,
			boolean includeBooleanValues) {
		return new AdvancedNodeCreator(featureModel, excludedFeatureNames, cnfType, modelType, includeBooleanValues).createNodes();
	}

	public static Node createNodes(FeatureModel featureModel, IFilter<Feature> featureFilter, CNFType cnfType, ModelType modelType, boolean includeBooleanValues) {
		return new AdvancedNodeCreator(featureModel, featureFilter, cnfType, modelType, includeBooleanValues).createNodes();
	}

	public static Node createNodesWithoutAbstract(FeatureModel featureModel) {
		AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel, new AbstractFeatureFilter());
		return nodeCreator.createNodes();
	}

	public static Node createNodesWithoutHidden(FeatureModel featureModel) {
		AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel, (new HiddenFeatureFilter()));
		return nodeCreator.createNodes();
	}

	private static Literal getVariable(Feature feature, boolean positive) {
		final String oldName = feature.getFeatureModel().getRenamingsManager().getOldName(feature.getName());
		return new Literal(oldName, positive);
	}

	private CNFType cnfType = CNFType.None;

	private ModelType modelType = ModelType.All;

	/**
	 * Specifies whether the literals <b>True</b> and <b>False</b> should be included in the created formula.</br>
	 * Default values is {@code true} (values will be included).
	 */
	private boolean includeBooleanValues = true;
	
	private boolean optionalRoot = false;

	private FeatureModel featureModel = null;

	private Collection<String> excludedFeatureNames = null;

	public AdvancedNodeCreator() {
	}

	public AdvancedNodeCreator(FeatureModel featureModel) {
		setFeatureModel(featureModel);
	}

	public AdvancedNodeCreator(FeatureModel featureModel, IFilter<Feature> featureFilter) {
		setFeatureModel(featureModel, featureFilter);
	}

	public AdvancedNodeCreator(FeatureModel featureModel, Collection<String> excludedFeatureNames) {
		setFeatureModel(featureModel, excludedFeatureNames);
	}

	public AdvancedNodeCreator(FeatureModel featureModel, Collection<String> excludedFeatureNames, CNFType cnfType, ModelType modelType,
			boolean includeBooleanValues) {
		this.cnfType = cnfType;
		this.modelType = modelType;
		this.includeBooleanValues = includeBooleanValues;
		setFeatureModel(featureModel, excludedFeatureNames);
	}

	public AdvancedNodeCreator(FeatureModel featureModel, IFilter<Feature> featureFilter, CNFType cnfType, ModelType modelType, boolean includeBooleanValues) {
		this.cnfType = cnfType;
		this.modelType = modelType;
		this.includeBooleanValues = includeBooleanValues;
		setFeatureModel(featureModel, featureFilter);
	}

	private And createConstraintNodes() {
		final List<Node> clauses = new ArrayList<>(featureModel.getConstraints().size());
		boolean compact = true;
		switch (cnfType) {
		case None:
			for (Constraint constraint : featureModel.getConstraints()) {
				clauses.add(constraint.getNode().clone());
			}
			break;
		case Regular:
			compact = false;
		case Compact:
		default:
			for (Constraint constraint : featureModel.getConstraints()) {
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

		if (excludedFeatureNames != null && !excludedFeatureNames.isEmpty()) {
			return LongRunningWrapper.runMethod(new FeatureRemover(new And(nodeArray), excludedFeatureNames, includeBooleanValues));
		} else {
			return new And(nodeArray);
		}
	}

	private And createStructuralNodes() {
		final Feature root = featureModel.getRoot();
		if (root != null) {
			final List<Node> clauses = new ArrayList<>(featureModel.getNumberOfFeatures());

			if (!optionalRoot) {
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

	public void setFeatureModel(FeatureModel featureModel) {
		this.featureModel = featureModel;
		this.excludedFeatureNames = null;
	}

	public void setFeatureModel(FeatureModel featureModel, IFilter<Feature> featureFilter) {
		this.featureModel = featureModel;
		this.excludedFeatureNames = Filter.toString(Filter.filter(new LinkedList<>(featureModel.getFeatures()), featureFilter));
	}

	public void setFeatureModel(FeatureModel featureModel, Collection<String> excludedFeatureNames) {
		this.featureModel = featureModel;
		this.excludedFeatureNames = excludedFeatureNames;
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
