/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis.cnf;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.ListIterator;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.NullMonitor;

/**
 * Removes features from a model while retaining dependencies of all other feature.
 *
 * @author Sebastian Krieter
 */
public class CNFCreator implements LongRunningMethod<CNF> {

	public static enum ModelType {
		All, NONE, OnlyConstraints, OnlyStructure
	}

	private IFeatureModel featureModel;

	private ModelType modelType;

	private boolean optionalRoot;
	private boolean useOldNames;

	public CNFCreator(IFeatureModel featureModel) {
		this(featureModel, ModelType.All, false, false);
	}

	public CNFCreator(IFeatureModel featureModel, ModelType modelType) {
		this(featureModel, modelType, false, false);
	}

	public CNFCreator(IFeatureModel featureModel, ModelType modelType, boolean useOldNames, boolean optionalRoot) {
		this.modelType = modelType;
		this.useOldNames = useOldNames;
		setOptionalRoot(optionalRoot);
		this.featureModel = featureModel;
	}

	public static CNF createNodes(IFeatureModel featureModel) {
		return new CNFCreator(featureModel).createNodes(new NullMonitor());
	}

	public CNF createNodes() {
		return createNodes(new NullMonitor());
	}

	public CNF createNodes(IMonitor monitor) {
		if (featureModel == null) {
			return new CNF(new Variables(Collections.<String> emptyList()));
		}

		final CNF cnf = new FeatureModelCNF(featureModel, useOldNames);
		final IVariables vars = cnf.getVariables();

		monitor.setTaskName("Creating Formula");
		monitor.setRemainingWork(2);
		final List<LiteralSet> andChildren1;
		final List<LiteralSet> andChildren2;

		switch (modelType) {
		case All:
			andChildren1 = createStructuralNodes(vars);
			andChildren2 = createConstraintNodes(vars);
			break;
		case OnlyConstraints:
			andChildren1 = Collections.emptyList();
			andChildren2 = createConstraintNodes(vars);
			break;
		case OnlyStructure:
			andChildren1 = createStructuralNodes(vars);
			andChildren2 = Collections.emptyList();
			break;
		case NONE:
		default:
			andChildren1 = Collections.emptyList();
			andChildren2 = Collections.emptyList();
			break;
		}
		monitor.step();

		cnf.addClauses(andChildren1);
		cnf.addClauses(andChildren2);

		monitor.step();

		return cnf;
	}

	@Override
	public CNF execute(IMonitor monitor) throws Exception {
		return createNodes(monitor);
	}

	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	public ModelType getModelType() {
		return modelType;
	}

	public boolean isOptionalRoot() {
		return optionalRoot;
	}

	public boolean isUseOldNames() {
		return useOldNames;
	}

	public void setFeatureModel(IFeatureModel featureModel) {
		this.featureModel = featureModel;
	}

	public void setModelType(ModelType modelType) {
		this.modelType = modelType;
	}

	public void setOptionalRoot(boolean optionalRoot) {
		this.optionalRoot = optionalRoot;
	}

	public void setUseOldNames(boolean useOldNames) {
		this.useOldNames = useOldNames;
	}

	private List<LiteralSet> createConstraintNodes(IVariables s) {
		final List<LiteralSet> clauses = new ArrayList<>(featureModel.getConstraints().size());
		for (final IConstraint constraint : featureModel.getConstraints()) {
			final Node node = constraint.getNode();
			getClauseFromNode(s, clauses, node);
		}
		return clauses;
	}

	public static void getClauseFromNode(IVariables s, final Collection<LiteralSet> clauses, final Node node) {
		final Node cnfNode = Node.buildCNF(node);
		// final Node cnfNode = node.toCNF();
		if (cnfNode instanceof And) {
			for (final Node andChild : cnfNode.getChildren()) {
				clauses.add(getClause(s, andChild));
			}
		} else {
			clauses.add(getClause(s, cnfNode));
		}
	}

	private List<LiteralSet> createStructuralNodes(IVariables s) {
		final IFeature root = FeatureUtils.getRoot(featureModel);
		if (root != null) {
			final List<LiteralSet> clauses = new ArrayList<>(featureModel.getNumberOfFeatures());

			clauses.add(new LiteralSet(s.getVariable(root.getName())));

			final Iterable<IFeature> features = featureModel.getFeatures();
			for (final IFeature feature : features) {
				for (final IFeatureStructure child : feature.getStructure().getChildren()) {
					clauses.add(new LiteralSet(-s.getVariable(child.getFeature().getName()), s.getVariable(feature.getName())));
				}

				if (feature.getStructure().hasChildren()) {
					if (feature.getStructure().isAnd()) {
						for (final IFeatureStructure child : feature.getStructure().getChildren()) {
							if (child.isMandatory()) {
								clauses.add(new LiteralSet(s.getVariable(child.getFeature().getName()), -s.getVariable(feature.getName())));
							}
						}
					} else if (feature.getStructure().isOr()) {
						final int[] orLiterals = new int[feature.getStructure().getChildrenCount() + 1];
						int i = 0;
						for (final IFeatureStructure child : feature.getStructure().getChildren()) {
							orLiterals[i++] = s.getVariable(child.getFeature().getName());
						}
						orLiterals[i] = -s.getVariable(feature.getName());
						clauses.add(new LiteralSet(orLiterals));
					} else if (feature.getStructure().isAlternative()) {
						final int[] alternativeLiterals = new int[feature.getStructure().getChildrenCount() + 1];
						int i = 0;
						for (final IFeatureStructure child : feature.getStructure().getChildren()) {
							alternativeLiterals[i++] = s.getVariable(child.getFeature().getName());
						}
						alternativeLiterals[i] = -s.getVariable(feature.getName());
						clauses.add(new LiteralSet(alternativeLiterals));

						for (final ListIterator<IFeatureStructure> it1 = feature.getStructure().getChildren().listIterator(); it1.hasNext();) {
							final IFeatureStructure fs = it1.next();
							for (final ListIterator<IFeatureStructure> it2 = feature.getStructure().getChildren().listIterator(it1.nextIndex()); it2
									.hasNext();) {
								clauses.add(new LiteralSet(-s.getVariable(fs.getFeature().getName()), -s.getVariable(it2.next().getFeature().getName())));
							}
						}
					}
				}
			}

			return clauses;
		}
		return Collections.emptyList();
	}

	private static LiteralSet getClause(IVariables s, Node andChild) {
		int absoluteValueCount = 0;
		boolean valid = true;

		final Literal[] children = (andChild instanceof Or) ? Arrays.copyOf(andChild.getChildren(), andChild.getChildren().length, Literal[].class)
			: new Literal[] { (Literal) andChild };

		for (int j = 0; j < children.length; j++) {
			final Literal literal = children[j];

			// sort out obvious tautologies
			if (literal.var.equals(NodeCreator.varTrue)) {
				if (literal.positive) {
					valid = false;
				} else {
					absoluteValueCount++;
					children[j] = null;
				}
			} else if (literal.var.equals(NodeCreator.varFalse)) {
				if (literal.positive) {
					absoluteValueCount++;
					children[j] = null;
				} else {
					valid = false;
				}
			}
		}

		if (valid) {
			if (children.length == absoluteValueCount) {
				throw new RuntimeException("Model is void!");
			}
			final int[] newChildren = new int[children.length - absoluteValueCount];
			int k = 0;
			for (int j = 0; j < children.length; j++) {
				final Literal literal = children[j];
				if (literal != null) {
					final int variable = s.getVariable(literal.var.toString());
					newChildren[k++] = literal.positive ? variable : -variable;
				}
			}
			return new LiteralSet(newChildren);
		} else {
			return null;
		}
	}

}
