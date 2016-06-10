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
package de.ovgu.featureide.fm.core.conf;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.conf.nodes.Expression;
import de.ovgu.featureide.fm.core.conf.nodes.Not2;
import de.ovgu.featureide.fm.core.conf.nodes.Or2;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.conf.nodes.Xor;
import de.ovgu.featureide.fm.core.conf.worker.CalcFixedThread;
import de.ovgu.featureide.fm.core.conf.worker.DFSThread;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.io.FeatureGraphFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

public class CreateFeatureGraphJob extends AProjectJob<CreateFeatureGraphJob.Arguments> implements LongRunningMethod<IFeatureGraph> {

	public static class Arguments extends JobArguments {
		private final IFeatureModel featureModel;

		public Arguments(IFeatureModel featureModel) {
			super(Arguments.class);
			this.featureModel = featureModel;
		}
	}

	private final Collection<IFeature> fixedFeatures = new HashSet<>();
	private final Collection<IFeature> coreFeatures = new HashSet<>();
	private final Collection<IFeature> deadFeatures = new HashSet<>();
	private IFeatureGraph featureGraph = null;

	private final HashSet<IFeature> processedParents = new HashSet<>();

	protected CreateFeatureGraphJob(Arguments arguments) {
		super("Spliting Feature Model", arguments);
	}

	@Override
	public IFeatureGraph execute(IMonitor workMonitor) throws Exception {
		return createFeatureGraph(workMonitor);
	}

	protected IFeatureGraph createFeatureGraph(IMonitor workMonitor) {
		workMonitor.setRemainingWork((2 * arguments.featureModel.getNumberOfFeatures()) + 1);

		final CalcFixedThread calcThread = new CalcFixedThread(AdvancedNodeCreator.createCNF(arguments.featureModel), workMonitor);
		calcThread.addObjects(arguments.featureModel.getFeatureTable().keySet());
		calcThread.start();

		for (Literal literal : calcThread.getFixedLiterals()) {
			final IFeature feature = arguments.featureModel.getFeature((String) literal.var);
			if (literal.positive) {
				coreFeatures.add(feature);
			} else {
				deadFeatures.add(feature);
			}
		}

		fixedFeatures.addAll(coreFeatures);
		fixedFeatures.addAll(deadFeatures);
		final List<IConstraint> constraints = arguments.featureModel.getConstraints();
		
		final Collection<IFeature> features = Functional.toList(arguments.featureModel.getFeatures());
		features.removeAll(fixedFeatures);

		processedParents.clear();

		workMonitor.setRemainingWork(arguments.featureModel.getNumberOfFeatures() + features.size() + 1);

		featureGraph = new MatrixFeatureGraph(arguments.featureModel, features, coreFeatures, deadFeatures);

		workMonitor.worked();

		VariableConfiguration conf = new VariableConfiguration(features.size());

		for (IFeature feature : features) {
			final IFeatureStructure parent = feature.getStructure().getParent();
			final String featureName = feature.getName();
			final String parentName = parent.getFeature().getName();

			// count non dead siblings of the current features
			int nonDeadSibilingCount = 0;
			for (IFeatureStructure sibiling : parent.getChildren()) {
				if (!deadFeatures.contains(sibiling.getFeature())) {
					nonDeadSibilingCount++;
				}
			}

			// connect current feature to parent
			if (!coreFeatures.contains(parent.getFeature())) {
				featureGraph.implies(featureName, parentName);
				if (parent.isAnd()) {
					if (feature.getStructure().isMandatory()) {
						featureGraph.implies(parentName, featureName);
					}
				} else {
					if (nonDeadSibilingCount == 1) {
						featureGraph.implies(parentName, featureName);
					} else {
						featureGraph.setEdge(parentName, featureName, MatrixFeatureGraph.EDGE_11Q);
						featureGraph.setEdge(featureName, parentName, MatrixFeatureGraph.EDGE_00Q);
					}
				}
			}

			// connect current feature to siblings
			if (nonDeadSibilingCount > 1) {
				if (parent.isAlternative()) {
					// XOR between two children
					if (coreFeatures.contains(parent.getFeature()) && nonDeadSibilingCount == 2) {
						for (IFeatureStructure sibiling : parent.getChildren()) {
							if (!deadFeatures.contains(sibiling.getFeature())) {
								featureGraph.setEdge(featureName, sibiling.getFeature().getName(), MatrixFeatureGraph.EDGE_10);
								featureGraph.setEdge(featureName, sibiling.getFeature().getName(), MatrixFeatureGraph.EDGE_01);
							}
						}
					} else {
						for (IFeatureStructure sibiling : parent.getChildren()) {
							if (!deadFeatures.contains(sibiling.getFeature())) {
								featureGraph.setEdge(featureName, sibiling.getFeature().getName(), MatrixFeatureGraph.EDGE_10);
								featureGraph.setEdge(featureName, sibiling.getFeature().getName(), MatrixFeatureGraph.EDGE_01Q);
							}
						}

						if (processedParents.add(parent.getFeature())) {
							final ArrayList<Variable> list = new ArrayList<>(nonDeadSibilingCount + 1);
							for (IFeatureStructure sibiling : parent.getChildren()) {
								if (!deadFeatures.contains(sibiling.getFeature())) {
									list.add(conf.getVariable(featureGraph.getFeatureIndex(sibiling.getFeature().getName())));
								}
							}
							if (!coreFeatures.contains(parent.getFeature())) {
								list.add(new Not2(conf.getVariable(featureGraph.getFeatureIndex(parent.getFeature().getName()))));
							}
							expList.add(new Xor(list.toArray(new Variable[0])));
						}
					}
				} else if (parent.isOr()) {
					// TODO atomic set would be better than core feature
					boolean optionalFeature = false;
					for (IFeatureStructure sibiling : parent.getChildren()) {
						if (coreFeatures.contains(sibiling.getFeature())) {
							optionalFeature = true;
							break;
						}
					}
					if (!optionalFeature) {
						for (IFeatureStructure sibiling : parent.getChildren()) {
							if (!deadFeatures.contains(sibiling.getFeature())) {
								featureGraph.setEdge(featureName, sibiling.getFeature().getName(), MatrixFeatureGraph.EDGE_01Q);
							}
						}

						if (processedParents.add(parent.getFeature())) {
							final ArrayList<Variable> list = new ArrayList<>(nonDeadSibilingCount);
							for (IFeatureStructure sibiling : parent.getChildren()) {
								if (!deadFeatures.contains(sibiling.getFeature())) {
									list.add(conf.getVariable(featureGraph.getFeatureIndex(sibiling.getFeature().getName())));
								}
							}
							final Or2 or2 = new Or2(list.toArray(new Variable[0]));
							if (coreFeatures.contains(parent.getFeature())) {
								expList.add(or2);
							} else {
								expList.add(new Xor(new Variable[] { or2, new Not2(conf.getVariable(featureGraph.getFeatureIndex(parent.getFeature().getName()))) }));
							}
						}
					}
				}
			}
		}

		for (IConstraint constraint : constraints) {
			connect(constraint.getNode(), conf);
		}

		final ArrayList<LinkedList<Expression>> expListAr = featureGraph.getExpListAr();
		for (Expression exp : expList) {
			for (Integer i : exp.getVariables()) {
				LinkedList<Expression> varExpList = expListAr.get(i);
				if (varExpList == null) {
					varExpList = new LinkedList<Expression>();
					expListAr.set(i, varExpList);
				}
				varExpList.add(exp);
			}
		}

		final ArrayList<String> featureNames = new ArrayList<>();
		for (IFeature feature : features) {
			featureNames.add(feature.getName());
		}

		if (featureGraph instanceof MatrixFeatureGraph) {
			final DFSThread dfsThread = new DFSThread((MatrixFeatureGraph) featureGraph, workMonitor);
			dfsThread.addObjects(featureNames);
			dfsThread.start();
		}

		return featureGraph;
	}

	protected boolean work(Path path, IMonitor workMonitor) throws Exception {
		final FeatureGraphFormat format = new FeatureGraphFormat();
		if (!FileHandler.load(path, featureGraph, format).containsError()) {
			createFeatureGraph(workMonitor);
			FileHandler.save(path, featureGraph, format);
		}
		return true;
	}

	private void buildClique(Node... nodes) {
		final Node cnfNode = new And(nodes).toCNF();

		if (cnfNode instanceof And) {
			for (Node andChild : cnfNode.getChildren()) {
				buildOrNode(andChild);
			}
		} else {
			buildOrNode(cnfNode);
		}
	}

	private void buildOrNode(Node andChild) {
		if (andChild instanceof Or) {
			boolean optionalFeature = false;
			for (Node orChild : andChild.getChildren()) {
				final Literal literal = (Literal) orChild;
				if ((literal.positive && coreFeatures.contains((arguments.featureModel.getFeature((String) literal.var))))
						|| (!literal.positive && deadFeatures.contains((arguments.featureModel.getFeature((String) literal.var))))) {
					optionalFeature = true;
					break;
				}
			}

			if (!optionalFeature) {
				for (Node orChild1 : andChild.getChildren()) {
					final Literal literal1 = (Literal) orChild1;
					final String featureName1 = (String) literal1.var;
					if (!fixedFeatures.contains(arguments.featureModel.getFeature(featureName1))) {
						for (Node orChild2 : andChild.getChildren()) {
							final Literal literal2 = (Literal) orChild2;
							final String featureName2 = (String) literal2.var;
							if (!fixedFeatures.contains(arguments.featureModel.getFeature(featureName2))) {
								featureGraph.setEdge(featureName1, featureName2, literal1.positive ? literal2.positive ? AFeatureGraph.EDGE_01Q
										: AFeatureGraph.EDGE_00Q : literal2.positive ? AFeatureGraph.EDGE_11Q : AFeatureGraph.EDGE_10Q);
							}
						}
					}
				}
			}
		}
	}

	private void imply(Literal implyNode, Literal impliedNode) {
		int negation = 0;
		if (!impliedNode.positive) {
			negation += 1;
		}
		if (!implyNode.positive) {
			negation += 2;
		}
		final String implyFeatureName = (String) implyNode.var;
		final String impliedFeatureName = (String) impliedNode.var;
		if (!fixedFeatures.contains(arguments.featureModel.getFeature(implyFeatureName))
				&& !fixedFeatures.contains(arguments.featureModel.getFeature(impliedFeatureName))) {
			featureGraph.implies(implyFeatureName, impliedFeatureName, negation);
		}
	}

	private Collection<Node> simplify(Node node) {
		final Collection<Node> nodeList = new LinkedList<>();
		node = Node.buildCNF(node);

		//		node = deMorgan(node);
		node = orToImply(node);
		node = elimnateNot(node);
		if (node instanceof And) {
			final Node[] children = node.getChildren();
			for (Node child : children) {
				nodeList.add(child);
			}
		} else {
			nodeList.add(node);
		}

		return nodeList;
	}

	private Node elimnateNot(Node node) {
		if (node instanceof Not) {
			Node child = node.getChildren()[0];
			if (child instanceof Literal) {
				Literal l = (Literal) child;
				return new Literal(l.var, !l.positive);
			} else if (child instanceof Not) {
				return child.getChildren()[0].clone();
			}
		}
		final Node[] children = node.getChildren();
		if (children != null) {
			for (int i = 0; i < children.length; i++) {
				children[i] = elimnateNot(children[i]);
			}
		}
		return node;
	}

	//	private Node deMorgan(Node node) {
	//		if (node instanceof Not) {
	//			Node child = node.getChildren()[0];
	//			if (child instanceof And) {
	//				final Node[] children = child.getChildren();
	//				final Node[] newChildren = new Node[children.length];
	//				for (int i = 0; i < children.length; i++) {
	//					newChildren[i] = new Not(children[i].clone());
	//				}
	//				node = new Or(newChildren);
	//			}
	//		}
	//		final Node[] children = node.getChildren();
	//		if (children != null) {
	//			for (int i = 0; i < children.length; i++) {
	//				children[i] = deMorgan(children[i]);
	//			}
	//		}
	//		return node;
	//	}

	private Node orToImply(Node node) {
		if (node instanceof Or && node.getChildren().length == 2) {
			final Node[] children = node.getChildren();
			return new Implies(new Not(children[0].clone()), children[1].clone());
		} else if (node instanceof And) {
			final Node[] children = node.getChildren();
			for (int i = 0; i < children.length; i++) {
				children[i] = orToImply(children[i]);
			}
		}
		return node;
	}

	private void connect(Node constraintNode2, VariableConfiguration conf) {
		//TODO simplify nodes: convert to implies, remove not node
		final Collection<Node> nodeList = simplify(constraintNode2);
		boolean builtClique = false;
		for (Node constraintNode : nodeList) {
			if (constraintNode instanceof Implies) {
				final Node leftNode = constraintNode.getChildren()[0];
				final Node rightNode = constraintNode.getChildren()[1];
				if (leftNode instanceof Literal) {
					final Literal implyNode = (Literal) leftNode;
					if (rightNode instanceof Literal) {
						imply(implyNode, (Literal) rightNode);
					} else if (rightNode instanceof And) {
						for (Node impliedNode : rightNode.getChildren()) {
							if (impliedNode instanceof Literal) {
								imply(implyNode, (Literal) impliedNode);
							} else {
								buildClique(implyNode, impliedNode);
								builtClique = true;
							}
						}
					}
				} else if (leftNode instanceof Or) {
					if (rightNode instanceof Literal) {
						for (Node implyNode : leftNode.getChildren()) {
							if (implyNode instanceof Literal) {
								imply((Literal) implyNode, (Literal) rightNode);
							} else {
								buildClique(implyNode, rightNode);
								builtClique = true;
							}
						}
					} else if (rightNode instanceof And) {
						for (Node implyNode : leftNode.getChildren()) {
							if (implyNode instanceof Literal) {
								for (Node impliedNode : rightNode.getChildren()) {
									if (impliedNode instanceof Literal) {
										imply((Literal) implyNode, (Literal) impliedNode);
									} else {
										buildClique(implyNode, impliedNode);
										builtClique = true;
									}
								}
							} else {
								for (Node impliedNode : rightNode.getChildren()) {
									buildClique(implyNode, impliedNode);
									builtClique = true;
								}
							}
						}
					}
				}
			} else {
				//TODO Implement other special cases
				buildClique(constraintNode);
				builtClique = true;
			}
			if (builtClique) {
				final Node cnfNode = constraintNode.clone().toCNF();
				if (cnfNode instanceof And) {
					for (Node andChild : cnfNode.getChildren()) {
						convertNode(conf, andChild);
					}
				} else if (cnfNode instanceof Or) {
					convertNode(conf, cnfNode);
				}
			}
		}
	}

	private final List<Expression> expList = new ArrayList<>();

	private void convertNode(VariableConfiguration conf, Node andChild) {
		final ArrayList<Variable> list = new ArrayList<>(andChild.getChildren().length);
		for (Node orChild : andChild.getChildren()) {
			final String featureName = ((Literal) orChild).var.toString();
			final IFeature feature = arguments.featureModel.getFeature(featureName);
			if (feature == null || coreFeatures.contains(feature)) {
				return;
			}
			if (deadFeatures.contains(feature)) {
				continue;
			}
			list.add(conf.getVariable(featureGraph.getFeatureIndex(featureName)));
		}
		expList.add(new Or2(list.toArray(new Variable[0])));
	}

}
