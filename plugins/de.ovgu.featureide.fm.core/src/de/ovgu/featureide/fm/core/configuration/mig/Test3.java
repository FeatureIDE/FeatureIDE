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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.sat4j.core.VecInt;
import org.sat4j.specs.IteratorInt;

import de.ovgu.featureide.fm.core.editing.cnf.Clause;

/**
 * TODO description
 *
 * @author skrieter
 */
public class Test3 {

	public static void main(String[] args) throws IOException {
		mig = Test2.getMIG();
		bfs2();
	}

	private static ModalImplicationGraph mig;

	private static void bfs2() {
		final int[] model = new int[mig.getAdjList().size() / 2];
		for (final Vertex vertex : mig.getAdjList()) {
			criticalPaths.clear();
			bfs2_inc(vertex);

			final HashSet<Vertex> reachableVertices = getReachableVertices(model, vertex, null);
//			final HashSet<Vertex> reachableVertices = new HashSet<>(criticalPaths.keySet());
//			reachableVertices.add(vertex);
//			reachableVertices.add(mig.getVertex(-vertex.getLiteral()));
			for (final Iterator<Entry<Vertex, Set<Vertex>>> iterator = criticalPaths.entrySet().iterator(); iterator.hasNext();) {
				if (iterator.next().getValue().size() <= 1) {
					iterator.remove();
				}
			}

			System.out.println(vertex + ":");
			final HashSet<Vertex> cn = new HashSet<>();
			if (!criticalPaths.isEmpty()) {
				for (final Iterator<Entry<Vertex, Set<Vertex>>> iterator = criticalPaths.entrySet().iterator(); iterator.hasNext();) {
					final Entry<Vertex, Set<Vertex>> entry = iterator.next();
					cn.addAll(entry.getValue());
					System.out.println("\t" + entry.getKey() + " -> " + entry.getValue());
				}

				for (final Iterator<Vertex> iterator = cn.iterator(); iterator.hasNext();) {
					final Vertex vertex2 = iterator.next();
					final HashSet<Vertex> reachableVertices2 = getReachableVertices(model, vertex, vertex2);
					reachableVertices2.add(vertex2);
					if (reachableVertices.equals(reachableVertices2)) {
						iterator.remove();
					}
				}
			}
			System.out.println("\t(" + cn.size() + ") " + cn);
		}
	}

	private static HashSet<Vertex> getReachableVertices(final int[] model, final Vertex vertex, Vertex forbiddenVertex) {
		Arrays.fill(model, 0);
		final int index = Math.abs(vertex.getLiteral()) - 1;
		model[index] = vertex.getLiteral();
		return bfs3_inc(vertex, forbiddenVertex);
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

	private static void bfs2_inc(Vertex rootVertex) {
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
					if (addPath2(curLevel, vertex)) {
						adjacentVertices.add(vertex);
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
						if (addPath2(curLevel, vertex)) {
							adjacentVertices.add(vertex);
						}
					}
				} else {
					for (final IteratorInt iterator = v.iterator(); iterator.hasNext();) {
						final int literal = iterator.next();
						final Vertex vertex = mig.getVertex(literal);
						if (!curLevel.visited(vertex)) {
							if (addPath2(curLevel, vertex)) {
								adjacentVertices.add(vertex);
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

	private static boolean addPath2(Level level, final Vertex vertex) {
		final Set<Vertex> criticalPath = criticalPaths.get(vertex);
		if (criticalPath == null) {
			final Set<Vertex> pathVertices = level.getPathVertices();
			criticalPaths.put(vertex, pathVertices);
			return true;
		} else {
			final Set<Vertex> pathVertices = level.getPathVertices();
			criticalPath.retainAll(pathVertices);
			return false;
		}
	}

	private static final HashMap<Vertex, Set<Vertex>> criticalPaths = new HashMap<>();

	private static HashSet<Vertex> bfs3_inc(Vertex rootVertex, Vertex forbiddenVertex) {
		final HashSet<Vertex> visited = new HashSet<>();
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
					if ((forbiddenVertex != vertex) && visited.add(vertex)) {
						adjacentVertices.add(vertex);
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
						if ((forbiddenVertex != vertex) && visited.add(vertex)) {
							adjacentVertices.add(vertex);
						}
					}
				} else {
					for (final IteratorInt iterator = v.iterator(); iterator.hasNext();) {
						final int literal = iterator.next();
						final Vertex vertex = mig.getVertex(literal);
						if (!curLevel.visited(vertex)) {
							if ((forbiddenVertex != vertex) && visited.add(vertex)) {
								adjacentVertices.add(vertex);
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
		return visited;
	}

}
