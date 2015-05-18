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
package de.ovgu.featureide.fm.core.conf;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.conf.nodes.Expression;
import de.ovgu.featureide.fm.core.conf.nodes.Not2;
import de.ovgu.featureide.fm.core.conf.nodes.Or2;
import de.ovgu.featureide.fm.core.conf.nodes.Variable;
import de.ovgu.featureide.fm.core.conf.nodes.VariableConfiguration;
import de.ovgu.featureide.fm.core.conf.nodes.Xor;
import de.ovgu.featureide.fm.core.conf.worker.DFSThread;
import de.ovgu.featureide.fm.core.conf.worker.base.ThreadPool;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

public class CreateFeatureGraphJob extends AProjectJob<CreateFeatureGraphJob.Arguments> {

	public static class Arguments extends JobArguments {
		private final FeatureModel featureModel;

		public Arguments(FeatureModel featureModel) {
			super(Arguments.class);
			this.featureModel = featureModel;
		}
	}

	private final Collection<Feature> fixedFeatures = new HashSet<>();
	private final Collection<Feature> coreFeatures = new HashSet<>();
	private final Collection<Feature> deadFeatures = new HashSet<>();
	private FeatureGraph featureGraph = null;

	private final HashSet<Feature> processedParents = new HashSet<>();

	protected CreateFeatureGraphJob(Arguments arguments) {
		super("Spliting Feature Model", arguments);
	}

	private boolean loadFeatureGraph() {
		try (final ObjectInputStream in = new ObjectInputStream(new FileInputStream(project.getFile("model.fg").getLocation().toFile()))) {
			this.featureGraph = (FeatureGraph) in.readObject();
			return true;
		} catch (IOException | ClassNotFoundException e) {
			FMCorePlugin.getDefault().logError(e);
			return false;
		}
	}

	public void writeFeatureGraph() {
		final IFile file = project.getFile("model.fg");
		try (final ObjectOutputStream out = new ObjectOutputStream(new FileOutputStream(file.getLocation().toFile()))) {
			out.writeObject(featureGraph);
			file.refreshLocal(IFile.DEPTH_ZERO, null);
		} catch (IOException | CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	protected boolean work() throws Exception {
		if (!loadFeatureGraph()) {
			System.out.println("Computing...");

			final List<List<Feature>> unnormalFeatures = arguments.featureModel.getAnalyser().analyzeFeatures();
			coreFeatures.addAll(unnormalFeatures.get(0)); //1548
			deadFeatures.addAll(unnormalFeatures.get(1)); //10
			fixedFeatures.addAll(coreFeatures);
			fixedFeatures.addAll(deadFeatures);
			final List<Constraint> constraints = arguments.featureModel.getConstraints();
			final Collection<Feature> features = new ArrayList<Feature>(arguments.featureModel.getFeatures());
			features.removeAll(fixedFeatures);

			processedParents.clear();

			workMonitor.setMaxAbsoluteWork(1 * features.size() + 1);

			featureGraph = new FeatureGraph(features);

			workMonitor.worked();

			VariableConfiguration conf = new VariableConfiguration(features.size());

			for (Feature feature : features) {
				final Feature parent = feature.getParent();
				final String featureName = feature.getName();
				final String parentName = parent.getName();

				// count non dead siblings of the current features
				int nonDeadSibilingCount = 0;
				for (Feature sibiling : parent.getChildren()) {
					if (!deadFeatures.contains(sibiling)) {
						nonDeadSibilingCount++;
					}
				}

				// connect current feature to parent
				if (!coreFeatures.contains(parent)) {
					featureGraph.implies(featureName, parentName);
					if (parent.isAnd()) {
						if (feature.isMandatory()) {
							featureGraph.implies(parentName, featureName);
						}
					} else {
						if (nonDeadSibilingCount == 1) {
							featureGraph.implies(parentName, featureName);
						} else {
							featureGraph.setEdge(parentName, featureName, FeatureGraph.EDGE_1q);
							featureGraph.setEdge(featureName, parentName, FeatureGraph.EDGE_0q);
						}
					}
				}

				// connect current feature to siblings
				if (nonDeadSibilingCount > 1) {
					if (parent.isAlternative()) {
						// XOR between two children
						if (coreFeatures.contains(parent) && nonDeadSibilingCount == 2) {
							for (Feature sibiling : parent.getChildren()) {
								if (!deadFeatures.contains(sibiling)) {
									featureGraph.setEdge(featureName, sibiling.getName(), FeatureGraph.EDGE_10);
									featureGraph.setEdge(featureName, sibiling.getName(), FeatureGraph.EDGE_01);
								}
							}
						} else {
							for (Feature sibiling : parent.getChildren()) {
								if (!deadFeatures.contains(sibiling)) {
									featureGraph.setEdge(featureName, sibiling.getName(), FeatureGraph.EDGE_10);
									featureGraph.setEdge(featureName, sibiling.getName(), FeatureGraph.EDGE_0q);
								}
							}

							if (processedParents.add(parent)) {
								final ArrayList<Variable> list = new ArrayList<>(nonDeadSibilingCount + 1);
								for (Feature sibiling : parent.getChildren()) {
									if (!deadFeatures.contains(sibiling)) {
										list.add(conf.getVariable(featureGraph.getFeatureIndex(sibiling.getName())));
									}
								}
								if (!coreFeatures.contains(parent)) {
									list.add(new Not2(conf.getVariable(featureGraph.getFeatureIndex(parent.getName()))));
								}
								expList.add(new Xor(list.toArray(new Variable[0])));
							}
						}
					} else if (parent.isOr()) {
						// TODO atomic set would be better than core feature
						boolean optionalFeature = false;
						for (Feature sibiling : parent.getChildren()) {
							if (coreFeatures.contains(sibiling)) {
								optionalFeature = true;
								break;
							}
						}
						if (!optionalFeature) {
							for (Feature sibiling : parent.getChildren()) {
								if (!fixedFeatures.contains(sibiling)) {
									featureGraph.setEdge(featureName, sibiling.getName(), FeatureGraph.EDGE_0q);
								}
							}

							if (processedParents.add(parent)) {
								final ArrayList<Variable> list = new ArrayList<>(nonDeadSibilingCount);
								for (Feature sibiling : parent.getChildren()) {
									if (!fixedFeatures.contains(sibiling)) {
										list.add(conf.getVariable(featureGraph.getFeatureIndex(sibiling.getName())));
									}
								}
								final Or2 or2 = new Or2(list.toArray(new Variable[0]));
								if (coreFeatures.contains(parent)) {
									expList.add(or2);
								} else {
									expList.add(new Xor(new Variable[] { or2, new Not2(conf.getVariable(featureGraph.getFeatureIndex(parent.getName()))) }));
								}
							}
						}
					}
				}
			}

			c1 = 0;
			c2 = 0;
			for (Constraint constraint : constraints) {
				connect(constraint.getNode(), conf);
			}

			System.out.println(c1);
			System.out.println(c2);
			System.out.println();

			final ArrayList<LinkedList<Expression>> expListAr = featureGraph.getExpListAr();
			for (Expression exp : expList) {
				for (Integer i : exp.getVaraibles()) {
					LinkedList<Expression> varExpList = expListAr.get(i);
					if (varExpList == null) {
						varExpList = new LinkedList<Expression>();
						expListAr.set(i, varExpList);
					}
					varExpList.add(exp);
				}
			}

			final ArrayList<String> featureNames = new ArrayList<>();
			for (Feature feature : features) {
				featureNames.add(feature.getName());
			}

			final ThreadPool<String> dfsThread = new ThreadPool<>(new DFSThread(featureGraph), workMonitor);
			dfsThread.addObjects(featureNames);
			dfsThread.run();

			writeFeatureGraph();
		}

		arguments.featureModel.setFeatureGraph(featureGraph);

		return true;
	}

	private void collectContainedFeatures(Node node, Set<String> featureNames) {
		if (node instanceof Literal) {
			featureNames.add((String) ((Literal) node).var);
		} else {
			for (Node child : node.getChildren()) {
				collectContainedFeatures(child, featureNames);
			}
		}
	}

	private void buildClique(Node... nodes) {
		final Set<String> featureNames = new HashSet<>();
		for (Node node : nodes) {
			collectContainedFeatures(node, featureNames);
		}
		for (Feature coreFeature : fixedFeatures) {
			featureNames.remove(coreFeature.getName());
		}
		for (String featureName1 : featureNames) {
			for (String featureName2 : featureNames) {
				featureGraph.setEdge(featureName1, featureName2, FeatureGraph.EDGE_0q);
				featureGraph.setEdge(featureName1, featureName2, FeatureGraph.EDGE_1q);
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
		node = node.clone().toCNF();

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
				c1++;
			} else {
				c2++;
			}
		}
	}

	private int c1, c2;

	private final List<Expression> expList = new ArrayList<>();

	private void convertNode(VariableConfiguration conf, Node andChild) {
		final ArrayList<Variable> list = new ArrayList<>(andChild.getChildren().length);
		for (Node orChild : andChild.getChildren()) {
			final String featureName = ((Literal) orChild).var.toString();
			final Feature feature = arguments.featureModel.getFeature(featureName);
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
