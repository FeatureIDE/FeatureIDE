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
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
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
import de.ovgu.featureide.fm.core.io.FileSystem;

/**
 * TODO description
 *
 * @author skrieter
 */
public class Test {

	public static void main(String[] args) throws IOException {
		mig = Test2.getMIG();

		dfs();
//		bfs2();
//		dfs2();
	}

	private static ModalImplicationGraph mig;

	public static void bfs() throws IOException {
		final Path outputFile = Paths.get("C:\\Users\\skrieter\\Desktop\\test.txt");
		FileSystem.delete(outputFile);
		final HashMap<Vertex, List<List<Vertex>>> shortestPaths = new HashMap<>();
		for (final Vertex vertex : mig.getAdjList()) {
			final List<List<Vertex>> bfs = bfs(vertex.getLiteral());
			shortestPaths.put(vertex, bfs);
			final StringBuilder sb = new StringBuilder();
			sb.append(vertex + ": \n");

			final ArrayList<Vertex> reachableVertices = new ArrayList<>(visitedVertices.keySet());
			Collections.sort(reachableVertices, new Comparator<Vertex>() {
				@Override
				public int compare(Vertex o1, Vertex o2) {
					return visitedVertices.get(o1) - visitedVertices.get(o2);
				}
			});
			sb.append("\t");
			for (final Vertex rv : reachableVertices) {
				sb.append(rv + " (" + visitedVertices.get(rv) + "), ");
			}
			sb.delete(sb.length() - 2, sb.length());
			sb.append("\n");
			for (final List<Vertex> list : bfs) {
				sb.append("\t" + list + "\n");
			}
//			FileSystem.append(outputFile, sb.toString().getBytes());
			System.out.println(sb.toString());
		}
	}

	private static final HashMap<Vertex, Integer> visitedVertices = new HashMap<>();
	private static final HashMap<Vertex, List<List<Vertex>>> visitedPaths = new HashMap<>();
	private static final HashMap<Vertex, Set<Vertex>> criticalPaths = new HashMap<>();

	private static List<List<Vertex>> bfs(int rootLiteral) {
		final List<List<Vertex>> shortestPathList = new ArrayList<>();

		final Vertex rootVertex = mig.getVertex(rootLiteral);

		visitedVertices.clear();
		final LinkedList<Vertex> q = new LinkedList<>();
		q.add(rootVertex);

		ArrayList<Vertex> curLevel = new ArrayList<>();
		curLevel.add(rootVertex);
		shortestPathList.add(curLevel);

		int numberOfVertexOnLevel = 0;
		while (!q.isEmpty()) {
			if (numberOfVertexOnLevel == 0) {
				numberOfVertexOnLevel = curLevel.size();
				curLevel = new ArrayList<>();
				shortestPathList.add(curLevel);
			}
			final Vertex curVertex = q.poll();

			for (final int strongEdge : curVertex.getStrongEdges()) {
				final Vertex vertex = mig.getVertex(strongEdge);
				curLevel.add(vertex);
				Integer count = visitedVertices.get(vertex);
				if (count == null) {
					count = 0;
					q.offer(vertex);
				}
				visitedVertices.put(vertex, count + 1);
			}

			// Weak Edges
			for (final int complexClauseIndex : curVertex.getComplexClauses()) {
				for (final int literal : mig.getComplexClauses().get(complexClauseIndex).getLiterals()) {
					if (literal != -curVertex.getLiteral()) {
						final Vertex vertex = mig.getVertex(literal);
						curLevel.add(vertex);
						Integer count = visitedVertices.get(vertex);
						if (count == null) {
							count = 0;
							q.offer(vertex);
						}
						visitedVertices.put(vertex, count + 1);
					}
				}
			}
			numberOfVertexOnLevel--;
		}
		return shortestPathList;
	}

	private static void dfs() {
		final LinkedList<Vertex> path = new LinkedList<>();
		final int[] model = new int[mig.getAdjList().size() / 2];
		for (final Vertex vertex : mig.getAdjList()) {
			visitedPaths.clear();
			path.addLast(vertex);
			final int index = Math.abs(vertex.getLiteral()) - 1;
			final int vertexValue = model[index];
			model[index] = vertex.getLiteral();
			dfs_rec(path, model);
			model[index] = vertexValue;
			path.removeLast();

			final ArrayList<Vertex> reachableVertices = new ArrayList<>(visitedPaths.keySet());
			Collections.sort(reachableVertices);

			final HashSet<Vertex> cn = new HashSet<>();
			System.out.println(vertex + ":");
			for (final Vertex rv : reachableVertices) {
				final List<List<Vertex>> curList = visitedPaths.get(rv);
				final Iterator<List<Vertex>> it = curList.iterator();
				List<Vertex> prefixPath = Collections.emptyList();
				if (it.hasNext()) {
					prefixPath = new ArrayList<>(it.next());
					while (it.hasNext()) {
						prefixPath.retainAll(it.next());
					}
				}
				if (prefixPath.size() > 1) {
					cn.addAll(prefixPath);
					System.out.println("\t" + rv + " -> " + prefixPath);
				}
			}
			System.out.println("\t(" + cn.size() + ") " + cn);

//			System.out.println(vertex + ":");
//			for (final Vertex rv : reachableVertices) {
//				final List<List<Vertex>> curList = visitedPaths.get(rv);
//				final Iterator<List<Vertex>> it = curList.iterator();
//				List<Vertex> prefixPath = Collections.emptyList();
//				if (it.hasNext()) {
//					prefixPath = new ArrayList<>(it.next());
//					while (it.hasNext()) {
//						prefixPath.retainAll(it.next());
//					}
//				}
//				if (prefixPath.size() > 1) {
//					System.out.println("\t(" + prefixPath.size() + ") " + rv + " -> " + prefixPath);
//				}
//			}
		}
	}

	private static void dfs_rec(LinkedList<Vertex> path, int[] model) {
//		System.out.println(path);
		final Vertex curVertex = path.getLast();
		final int[] curModel = Arrays.copyOf(model, model.length);
		final Collection<Vertex> adjacentVertices = new HashSet<>();

		for (final int strongEdge : curVertex.getStrongEdges()) {
			final Vertex vertex = mig.getVertex(strongEdge);
			if (!path.contains(vertex)) {
				curModel[Math.abs(vertex.getLiteral()) - 1] = vertex.getLiteral();
				addPath(path, adjacentVertices, vertex);
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
				if (!path.contains(vertex)) {
					curModel[Math.abs(vertex.getLiteral()) - 1] = vertex.getLiteral();
					addPath(path, adjacentVertices, vertex);
				}
			} else {
				for (final IteratorInt iterator = v.iterator(); iterator.hasNext();) {
					final int literal = iterator.next();
					final Vertex vertex = mig.getVertex(literal);
					if (!path.contains(vertex)) {
						addPath(path, adjacentVertices, vertex);
					}
				}
			}
		}

		for (final Vertex vertex : adjacentVertices) {
			final int index = Math.abs(vertex.getLiteral()) - 1;
			final int vertexValue = curModel[index];
			if (vertexValue != -vertex.getLiteral()) {
				path.addLast(vertex);
				curModel[index] = vertex.getLiteral();
				dfs_rec(path, curModel);
				curModel[index] = vertexValue;
				path.removeLast();
			}
		}

	}

	private static void addPath(LinkedList<Vertex> path, final Collection<Vertex> adjacentVertices, final Vertex vertex) {
		List<List<Vertex>> paths = visitedPaths.get(vertex);
		if (paths == null) {
			paths = new ArrayList<>();
			visitedPaths.put(vertex, paths);
		}
		boolean noShortherPath = true;
		for (final Iterator<List<Vertex>> it = paths.iterator(); it.hasNext();) {
			final List<Vertex> previousPath = it.next();
			if (path.containsAll(previousPath)) {
				noShortherPath = false;
				break;
			} else if (previousPath.containsAll(path)) {
				it.remove();
			}
		}
		if (noShortherPath) {
			adjacentVertices.add(vertex);
			paths.add(new ArrayList<>(path));
		}
	}

	private static void bfs2() {
		for (final Vertex vertex : mig.getAdjList()) {
			criticalPaths.clear();
			bfs2_inc(vertex);

			final ArrayList<Vertex> reachableVertices = new ArrayList<>(criticalPaths.keySet());
			Collections.sort(reachableVertices);

			System.out.println(vertex + ":");
			final HashSet<Vertex> cn = new HashSet<>();
			for (final Vertex rv : reachableVertices) {
				final Set<Vertex> criticalPath = criticalPaths.get(rv);
				if (criticalPath.size() > 1) {
					cn.addAll(criticalPath);
				}
			}
			System.out.println("\t(" + cn.size() + ") " + cn);

//			System.out.println(vertex + ":");
//			for (final Vertex rv : reachableVertices) {
//				final Set<Vertex> criticalPath = criticalPaths.get(rv);
//				if (criticalPath.size() > 1) {
//					System.out.println("\t(" + criticalPath.size() + ") " + rv + " -> " + criticalPath);
//				}
//			}
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

	private static final HashMap<Vertex, Collection<Vertex>> reachableVertices = new HashMap<>();
	private static final HashMap<Vertex, Collection<Vertex>> criticalVertices = new HashMap<>();

	private static void dfs2() {
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

		for (final Vertex vertex1 : mig.getAdjList()) {
			final Collection<Vertex> compare = reachableVertices.get(vertex1);
			final Collection<Vertex> critical = new ArrayList<>();
			criticalVertices.put(vertex1, critical);
			for (final Vertex vertex2 : mig.getAdjList()) {
				if ((vertex1 != vertex2) && compare.contains(vertex2)) {
					final int index = Math.abs(vertex1.getLiteral()) - 1;
					final int vertexValue = model[index];
					model[index] = vertex1.getLiteral();
					final HashSet<Vertex> reachable = new HashSet<>();
					dfs2_rec(vertex1, vertex2, reachable, model);
					reachable.add(vertex2);
					if (!compare.equals(reachable)) {
						critical.add(vertex2);
					}
					model[index] = vertexValue;
				}
			}
		}

		for (final Entry<Vertex, Collection<Vertex>> entry : criticalVertices.entrySet()) {
			System.out.println(entry.getKey() + ":\n\t(" + entry.getValue().size() + ") " + entry.getValue());
		}
	}

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
