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
package de.ovgu.featureide.fm.core.configuration.mig;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.prop4j.solver.SatInstance;
import org.sat4j.core.VecInt;
import org.sat4j.specs.IteratorInt;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.cnf.Clause;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * TODO description
 *
 * @author skrieter
 */
public class Test2 {

	private static final String prefix = "C:\\Users\\skrieter\\git\\FeatureIDE_mig\\plugins\\de.ovgu.featureide.examples\\featureide_examples\\";

	public static ModalImplicationGraph getMIG() {
		final String fileName = prefix +
//			"FeatureModels\\Automotive01\\model.xml";
//			"Notepad-FH-Java-2\\model.xml";
//			"GPL-FH-Java\\model.xml";
			"FeatureModels\\aaed2000\\model.xml";
		final IFeatureModel fm = FeatureModelManager.load(Paths.get(fileName)).getObject();

		System.out.println(fm.getNumberOfFeatures());
		final MIGBuilder migBuilder = new MIGBuilder(new SatInstance(AdvancedNodeCreator.createRegularCNF(fm)), false);
		return LongRunningWrapper.runMethod(migBuilder);
	}

	public static void main(String[] args) throws IOException {
		mig = getMIG();
		bfs2();
	}

	private static ModalImplicationGraph mig;

	private static void bfs2() {
		final int[] model = new int[mig.getAdjList().size() / 2];
		for (final Vertex vertex : mig.getAdjList()) {
			final int index = Math.abs(vertex.getLiteral()) - 1;
			final int vertexValue = model[index];
			model[index] = vertex.getLiteral();
			final HashSet<Vertex> reachable = new HashSet<>();
			dfs2_rec(vertex, null, reachable, model);
			reachableVertices.put(vertex, reachable);
			model[index] = vertexValue;
		}

		for (final Vertex vertex : mig.getAdjList()) {
			System.out.println(vertex + ":");
			final HashSet<Vertex> cn = new HashSet<>();
			for (final Vertex targetVertex : reachableVertices.get(vertex)) {
				if (vertex != targetVertex) {
					bfs2_inc(vertex, targetVertex);

					if ((curCriticalPath != null) && (curCriticalPath.size() > 1)) {
						cn.addAll(curCriticalPath);
						System.out.println("\t" + targetVertex + " -> " + curCriticalPath);
					}
				}
			}
			System.out.println("\t(" + cn.size() + ") " + cn);
		}
	}

	private static class Level {
		private final int depth;
		private final Level parent;
		private final Vertex vertex;
		private final int[] model;

		public Level(Level parent, Vertex vertex) {
			this.parent = parent;
			this.vertex = vertex;
			depth = (parent == null) ? 0 : parent.depth + 1;
			model = (parent == null) ? new int[mig.getAdjList().size() / 2] : Arrays.copyOf(parent.model, parent.model.length);
			model[Math.abs(vertex.getLiteral()) - 1] = vertex.getLiteral();
		}

		public Level descend(Vertex vertex) {
			return new Level(this, vertex);
		}

		public Set<Vertex> getPathVertices() {
			final HashSet<Vertex> vertices = new HashSet<>();
			Level level = this;
			do {
				vertices.add(level.vertex);
				level = level.parent;
			} while (level != null);
			return vertices;
		}

		public List<Vertex> getPath() {
			final List<Vertex> vertices = new ArrayList<>(depth + 1);
			Level level = this;
			do {
				vertices.add(level.vertex);
				level = level.parent;
			} while (level != null);
			Collections.reverse(vertices);
			return vertices;
		}

		public boolean visited(Vertex vertex) {
			Level level = this;
			do {
				if (level.vertex.equals(vertex)) {
					return true;
				}
				level = level.parent;
			} while (level != null);
			return false;
		}

		@Override
		public String toString() {
			return "Path " + getPath();
		}

	}

	private static final HashSet<Vertex> visited = new HashSet<>();
	private static HashSet<Vertex> curCriticalPath = null;

	private static void bfs2_inc(Vertex rootVertex, Vertex targetVertex) {
		visited.clear();
		curCriticalPath = null;
		final LinkedList<Level> levels = new LinkedList<>();
		levels.add(new Level(null, rootVertex));
		while (!levels.isEmpty()) {
			final Level curLevel = levels.poll();

			final Vertex curVertex = curLevel.vertex;
			final int[] curModel = curLevel.model;
			final Collection<Vertex> adjacentVertices = new HashSet<>();

			for (final int strongEdge : curVertex.getStrongEdges()) {
				final Vertex vertex = mig.getVertex(strongEdge);
				if (!curLevel.visited(vertex)) {
					curModel[Math.abs(vertex.getLiteral()) - 1] = vertex.getLiteral();
					final byte addPath2 = addPath2(curLevel, vertex, targetVertex);
					switch (addPath2) {
					case -1:
						return;
					case 0:
						break;
					case 1:
						adjacentVertices.add(vertex);
						break;
					}
				}
			}

			final int[] complexClauses = curVertex.getComplexClauses();
			// Weak Edges
			final VecInt v = new VecInt();
			outerLoop: for (int i = 0; i < complexClauses.length; i++) {
				final Clause clause = mig.getComplexClauses().get(complexClauses[i]);

				v.clear();
				final int[] literals = clause.getLiterals();
				for (int j = 0; j < literals.length; j++) {
					final int literal = literals[j];
					if (literal == -curVertex.getLiteral()) {
						continue;
					}
					final int value = curModel[Math.abs(literal) - 1];

					if (value == 0) {
						// add literal to list
						v.push(literal);
					} else {
						if (value == literal) {
							// Clause is satisfied
							continue outerLoop;
						} else {
							// Do nothing
						}
					}
				}

				if (v.size() == 1) {
					final int literal = v.get(0);
					final Vertex vertex = mig.getVertex(literal);
					if (!curLevel.visited(vertex)) {
						curModel[Math.abs(vertex.getLiteral()) - 1] = vertex.getLiteral();
						final byte addPath2 = addPath2(curLevel, vertex, targetVertex);
						switch (addPath2) {
						case -1:
							return;
						case 0:
							break;
						case 1:
							adjacentVertices.add(vertex);
							break;
						}
					}
				} else {
					for (final IteratorInt iterator = v.iterator(); iterator.hasNext();) {
						final int literal = iterator.next();
						final Vertex vertex = mig.getVertex(literal);
						if (!curLevel.visited(vertex)) {
							final byte addPath2 = addPath2(curLevel, vertex, targetVertex);
							switch (addPath2) {
							case -1:
								return;
							case 0:
								break;
							case 1:
								adjacentVertices.add(vertex);
								break;
							}
						}
					}
				}
			}

			for (final Vertex vertex : adjacentVertices) {
				final int index = Math.abs(vertex.getLiteral()) - 1;
				final int vertexValue = curModel[index];
				if (vertexValue != -vertex.getLiteral()) {
					levels.add(curLevel.descend(vertex));
				}
			}
		}
	}

	private static byte addPath2(Level level, final Vertex vertex, final Vertex targetVertex) {
		final Set<Vertex> pathVertices = level.getPathVertices();
		if (vertex == targetVertex) {
			if (curCriticalPath == null) {
				curCriticalPath = (HashSet<Vertex>) pathVertices;
			} else {
				curCriticalPath.retainAll(pathVertices);
				if (curCriticalPath.size() <= 1) {
					return -1;
				}
			}
			return 0;
		} else {
			return (byte) (!pathVertices.contains(targetVertex) && visited.add(vertex) ? 1 : 0);
		}
	}

	private static final HashMap<Vertex, Collection<Vertex>> reachableVertices = new HashMap<>();

	private static void dfs2_rec(Vertex curVertex, Vertex forbiddenVertex, HashSet<Vertex> reachable, int[] model) {
		reachable.add(curVertex);
		final int[] curModel = Arrays.copyOf(model, model.length);
		final Collection<Vertex> adjacentVertices = new HashSet<>();

		for (final int strongEdge : curVertex.getStrongEdges()) {
			final Vertex vertex = mig.getVertex(strongEdge);
			if (vertex != forbiddenVertex) {
				curModel[Math.abs(vertex.getLiteral()) - 1] = vertex.getLiteral();
				adjacentVertices.add(vertex);
			}
		}

		final int[] complexClauses = curVertex.getComplexClauses();
		// Weak Edges
		final VecInt v = new VecInt();
		outerLoop: for (int i = 0; i < complexClauses.length; i++) {
			final Clause clause = mig.getComplexClauses().get(complexClauses[i]);

			v.clear();
			final int[] literals = clause.getLiterals();
			for (int j = 0; j < literals.length; j++) {
				final int literal = literals[j];
				if (literal == -curVertex.getLiteral()) {
					continue;
				}
				final int value = curModel[Math.abs(literal) - 1];

				if (value == 0) {
					// add literal to list
					v.push(literal);
				} else {
					if (value == literal) {
						// Clause is satisfied
						continue outerLoop;
					} else {
						// Do nothing
					}
				}
			}

			if (v.size() == 1) {
				final int literal = v.get(0);
				final Vertex vertex = mig.getVertex(literal);
				if (vertex != forbiddenVertex) {
					curModel[Math.abs(vertex.getLiteral()) - 1] = vertex.getLiteral();
					adjacentVertices.add(vertex);
				}
			} else {
				for (final IteratorInt iterator = v.iterator(); iterator.hasNext();) {
					final int literal = iterator.next();
					final Vertex vertex = mig.getVertex(literal);
					if (vertex != forbiddenVertex) {
						adjacentVertices.add(vertex);
					}
				}
			}
		}

		for (final Vertex vertex : adjacentVertices) {
			final int index = Math.abs(vertex.getLiteral()) - 1;
			final int vertexValue = curModel[index];
			if ((vertexValue != -vertex.getLiteral()) && !reachable.contains(vertex)) {
				curModel[index] = vertex.getLiteral();
				dfs2_rec(vertex, forbiddenVertex, reachable, curModel);
				curModel[index] = vertexValue;
			}
		}
	}

}
