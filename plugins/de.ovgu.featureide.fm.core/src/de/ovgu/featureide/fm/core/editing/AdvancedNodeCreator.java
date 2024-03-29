/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

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

	private boolean omitRoot = false;

	public static Node createCNF(IFeatureModel featureModel) {
		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel);
		nodeCreator.setCnfType(CNFType.Compact);
		return nodeCreator.createNodes();
	}

	public static Node createRegularCNF(IFeatureModel featureModel) {
		final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel);
		nodeCreator.setCnfType(CNFType.Regular);
		nodeCreator.setIncludeBooleanValues(false);
		return nodeCreator.createNodes();
	}

	public static Node createNodes(IFeatureModel featureModel) {
		return new AdvancedNodeCreator(featureModel).createNodes();
	}

	private CNFType cnfType = CNFType.None;

	private ModelType modelType = ModelType.All;

	/**
	 * Specifies whether the literals <b>True</b> and <b>False</b> should be included in the created formula.<br> Default values is {@code true} (values will be
	 * included).
	 */
	private boolean includeBooleanValues = true;

	private boolean useOldNames = false;

	private boolean optionalRoot = false;

	private IFeatureModel featureModel = null;

	/** The trace model. */
	private FeatureModelToNodeTraceModel traceModel;
	/** True to create the trace model while creating nodes. */
	private boolean recordTraceModel = false;

	public AdvancedNodeCreator() {}

	public AdvancedNodeCreator(IFeatureModel featureModel) {
		setFeatureModel(featureModel);
	}

	public AdvancedNodeCreator(IFeatureModel featureModel, CNFType cnfType, ModelType modelType, boolean includeBooleanValues) {
		this.cnfType = cnfType;
		this.modelType = modelType;
		this.includeBooleanValues = includeBooleanValues;
		setFeatureModel(featureModel);
	}

	/**
	 * Creates the nodes for all constraints of the feature model.
	 *
	 * @return the transformed nodes
	 */
	private And createConstraintNodes() {
		final List<Node> clauses = new LinkedList<>();
		for (final IConstraint constraint : featureModel.getConstraints()) {
			createConstraintNodes(constraint, clauses, true);
		}
		return new And(clauses.toArray(new Node[clauses.size()]));
	}

	/**
	 * Creates the node for a single constraint of the feature model.
	 *
	 * @param constraint constraint to transform
	 * @return the transformed node
	 */
	public Node createConstraintNode(IConstraint constraint) {
		return createConstraintNode(constraint, true);
	}

	/**
	 * Creates the node for a single constraint of the feature model.
	 *
	 * @param constraint constraint to transform
	 * @param positive false to negate the node of the constraint before adding
	 * @return the transformed node
	 */
	public Node createConstraintNode(IConstraint constraint, boolean positive) {
		final List<Node> clauses = createConstraintNodes(constraint, new LinkedList<Node>(), positive);
		if ((cnfType != CNFType.Regular) && (clauses.size() == 1)) {
			return clauses.get(0);
		}
		return new And(clauses.toArray(new Node[clauses.size()]));
	}

	/**
	 * Creates the clauses for the given constraint. Adds them to the given list of clauses.
	 *
	 * @param constraint constraint to transform
	 * @param clauses clauses to add to; out variable
	 * @param positive false to negate the node of the constraint before adding
	 * @return given clauses plus new clauses
	 */
	private List<Node> createConstraintNodes(IConstraint constraint, List<Node> clauses, boolean positive) {
		Node clause = constraint.getNode();
		boolean compact = true;
		switch (cnfType) {
		case None:
			clause = clause.clone();
			if (!positive) {
				clause = new Not(clause);
			}
			clauses.add(clause);
			if (isRecordingTraceModel()) {
				traceModel.addTraceConstraint(constraint);
			}
			break;
		case Regular:
			compact = false;
		case Compact:
		default:
			if (!positive) {
				clause = new Not(clause);
			}
			final Node cnfNode = clause.toCNF();
			if (cnfNode instanceof And) {
				for (final Node andChild : cnfNode.getChildren()) {
					clause = compact || (andChild instanceof Or) ? andChild : new Or(andChild);
					clauses.add(clause);
					if (isRecordingTraceModel()) {
						traceModel.addTraceConstraint(constraint);
					}
				}
			} else {
				clause = compact || (cnfNode instanceof Or) ? cnfNode : new Or(cnfNode);
				clauses.add(clause);
				if (isRecordingTraceModel()) {
					traceModel.addTraceConstraint(constraint);
				}
			}
			break;
		}
		return clauses;
	}

	public Node createNodes() {
		return createNodes(new NullMonitor<>());
	}

	public Node createNodes(IMonitor<Node> monitor) {
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

	private Node[] createFormula(IMonitor<?> monitor) {
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
			Node clause;

			if (!optionalRoot && !(omitRoot && ((modelType != ModelType.All) || !rootInConstraints(root)))) {
				clause = getLiteral(root, true);
				switch (cnfType) {
				case Regular:
					clause = new Or(clause);
					break;
				case None:
				case Compact:
				default:
					break;
				}
				clauses.add(clause);
				if (isRecordingTraceModel()) {
					traceModel.addTraceRoot(root);
				}
			}

			final Iterable<IFeature> features = featureModel.getFeatures();
			for (final IFeature feature : features) {
				final IFeatureStructure structure = feature.getStructure();

				if (structure.hasChildren()) {
					if (!omitRoot || !structure.isRoot()) {
						for (final IFeatureStructure child : structure.getChildren()) {
							final IFeature childFeature = child.getFeature();
							clause = new Or(getLiteral(feature, true), getLiteral(childFeature, false));
							clauses.add(clause);
							if (isRecordingTraceModel()) {
								traceModel.addTraceChildUp(feature, Collections.singleton(childFeature));
							}
						}

						if (structure.isAnd()) {
							for (final IFeatureStructure child : structure.getChildren()) {
								if (child.isMandatory()) {
									final IFeature childFeature = child.getFeature();
									clause = new Or(getLiteral(childFeature, true), getLiteral(feature, false));
									clauses.add(clause);
									if (isRecordingTraceModel()) {
										traceModel.addTraceChildDown(feature, Collections.singleton(childFeature));
									}
								}
							}
						} else if (structure.isOr()) {
							final List<IFeature> children = new LinkedList<>();
							final Literal[] orLiterals = new Literal[structure.getChildren().size() + 1];
							int i = 0;
							for (final IFeatureStructure child : structure.getChildren()) {
								final IFeature childFeature = child.getFeature();
								orLiterals[i++] = getLiteral(childFeature, true);
								children.add(childFeature);
							}
							orLiterals[i] = getLiteral(feature, false);
							clause = new Or(orLiterals);
							clauses.add(clause);
							if (isRecordingTraceModel()) {
								traceModel.addTraceChildDown(feature, children);
							}
						} else if (structure.isAlternative()) {
							final List<IFeature> children = new LinkedList<>();
							final Literal[] alternativeLiterals = new Literal[structure.getChildrenCount() + 1];
							int i = 0;
							for (final IFeatureStructure child : structure.getChildren()) {
								final IFeature childFeature = child.getFeature();
								alternativeLiterals[i++] = getLiteral(childFeature, true);
								children.add(childFeature);
							}
							alternativeLiterals[i] = getLiteral(feature, false);
							clause = new Or(alternativeLiterals);
							clauses.add(clause);
							if (isRecordingTraceModel()) {
								traceModel.addTraceChildDown(feature, children);
							}

							for (final ListIterator<IFeatureStructure> it1 = structure.getChildren().listIterator(); it1.hasNext();) {
								final IFeatureStructure fs = it1.next();
								final IFeature sibling1 = fs.getFeature();
								for (final ListIterator<IFeatureStructure> it2 = structure.getChildren().listIterator(it1.nextIndex()); it2.hasNext();) {
									final IFeature sibling2 = it2.next().getFeature();
									clause = new Or(getLiteral(sibling1, false), getLiteral(sibling2, false));
									clauses.add(clause);
									if (isRecordingTraceModel()) {
										traceModel.addTraceChildHorizontal(Arrays.asList(sibling1, sibling2));
									}
								}
							}
						}
					} else {
						if (structure.isAnd()) {
							for (final IFeatureStructure child : structure.getChildren()) {
								if (child.isMandatory()) {
									final IFeature childFeature = child.getFeature();
									clause = new Or(getLiteral(childFeature, true));
									clauses.add(clause);
									if (isRecordingTraceModel()) {
										traceModel.addTraceChildDown(feature, Collections.singleton(childFeature));
									}
								}
							}
						} else if (structure.isOr()) {
							final List<IFeature> children = new LinkedList<>();
							final Literal[] orLiterals = new Literal[structure.getChildren().size()];
							int i = 0;
							for (final IFeatureStructure child : structure.getChildren()) {
								final IFeature childFeature = child.getFeature();
								orLiterals[i++] = getLiteral(childFeature, true);
								children.add(childFeature);
							}
							clause = new Or(orLiterals);
							clauses.add(clause);
							if (isRecordingTraceModel()) {
								traceModel.addTraceChildDown(feature, children);
							}
						} else if (structure.isAlternative()) {
							final List<IFeature> children = new LinkedList<>();
							final Literal[] alternativeLiterals = new Literal[structure.getChildrenCount()];
							int i = 0;
							for (final IFeatureStructure child : structure.getChildren()) {
								final IFeature childFeature = child.getFeature();
								alternativeLiterals[i++] = getLiteral(childFeature, true);
								children.add(childFeature);
							}
							clause = new Or(alternativeLiterals);
							clauses.add(clause);
							if (isRecordingTraceModel()) {
								traceModel.addTraceChildDown(feature, children);
							}

							for (final ListIterator<IFeatureStructure> it1 = structure.getChildren().listIterator(); it1.hasNext();) {
								final IFeatureStructure fs = it1.next();
								final IFeature sibling1 = fs.getFeature();
								for (final ListIterator<IFeatureStructure> it2 = structure.getChildren().listIterator(it1.nextIndex()); it2.hasNext();) {
									final IFeature sibling2 = it2.next().getFeature();
									clause = new Or(getLiteral(sibling1, false), getLiteral(sibling2, false));
									clauses.add(clause);
									if (isRecordingTraceModel()) {
										traceModel.addTraceChildHorizontal(Arrays.asList(sibling1, sibling2));
									}
								}
							}
						}
					}
				}
			}

			return new And(clauses.toArray(new Node[0]));
		}
		return new And(new Node[0]);
	}

	private boolean rootInConstraints(final IFeature root) {
		return featureModel.getConstraints().stream().anyMatch(c -> c.getContainedFeatures().contains(root));
	}

	private Literal getLiteral(IFeature feature, boolean positive) {
		return new Literal(useOldNames ? feature.getFeatureModel().getRenamingsManager().getOldName(feature.getName()) : feature.getName(), positive);
	}

	@Override
	public Node execute(IMonitor<Node> monitor) throws Exception {
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
	 * Returns whether the boolean primitives true and false should be included in the formula.
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
		traceModel = isRecordingTraceModel() ? new FeatureModelToNodeTraceModel() : null; // Reset the trace model.
	}

	/**
	 * Sets whether the boolean primitives true and false should be included in the formula.
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

	public boolean isOmitRoot() {
		return omitRoot;
	}

	public void setOmitRoot(boolean omitRoot) {
		this.omitRoot = omitRoot;
	}

	/**
	 * <p> Returns the trace model. The trace model keeps track of the origin of transformed elements. </p>
	 *
	 * <p> Building the trace model must have been {@link #setRecordTraceModel(boolean) enabled} prior to creating the nodes. As a performance concern, this is
	 * disabled by default. </p>
	 *
	 * @return the trace model
	 */
	public FeatureModelToNodeTraceModel getTraceModel() {
		return traceModel;
	}

	/**
	 * Returns true iff this creates a trace model while creating nodes. Defaults to false.
	 *
	 * @return true iff this creates a trace model while creating nodes
	 */
	public boolean isRecordingTraceModel() {
		return recordTraceModel;
	}

	/**
	 * Sets whether this should create a trace model while creating nodes.
	 *
	 * @param recordTraceModel whether to create a trace model while creating nodes
	 */
	public void setRecordTraceModel(boolean recordTraceModel) {
		final boolean old = this.recordTraceModel;
		this.recordTraceModel = recordTraceModel;
		if (old != recordTraceModel) {
			traceModel = isRecordingTraceModel() ? new FeatureModelToNodeTraceModel() : null; // Reset the trace model.
		}
	}

}
