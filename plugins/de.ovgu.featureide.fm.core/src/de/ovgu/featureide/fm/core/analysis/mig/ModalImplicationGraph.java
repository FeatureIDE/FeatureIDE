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
package de.ovgu.featureide.fm.core.analysis.mig;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.RuntimeContradictionException;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * Adjacency list implementation for a feature graph.
 *
 * @author Sebastian Krieter
 */
public class ModalImplicationGraph implements IEdgeTypes, Serializable {

	private static final long serialVersionUID = 5258868675944962032L;

	public static ModalImplicationGraph build(CNF satInstance, boolean detectStrong, boolean checkRedundancy) {
		final MIGBuilder migBuilder = new MIGBuilder(satInstance);
		migBuilder.setCheckRedundancy(checkRedundancy);
		migBuilder.setDetectStrong(detectStrong);
		return LongRunningWrapper.runMethod(migBuilder);
	}

	private final Set<LiteralSet> transitiveStrongEdges = new HashSet<>();
	final List<Vertex> adjList;
	final List<LiteralSet> complexClauses = new ArrayList<>(0);

	public ModalImplicationGraph() {
		adjList = new ArrayList<>(0);
	}

	public ModalImplicationGraph(int numVariables) {
		adjList = new ArrayList<>(numVariables);
	}

	public void copyValues(ModalImplicationGraph other) {
		adjList.addAll(other.adjList);
		complexClauses.addAll(other.complexClauses);
	}

	public Traverser traverse() {
		return new Traverser(this);
	}

	public Vertex getVertex(int literal) {
		return adjList.get(((Math.abs(literal) - 1) << 1) + (literal < 0 ? 0 : 1));
	}

	public List<Vertex> getAdjList() {
		return Collections.unmodifiableList(adjList);
	}

	public List<LiteralSet> getComplexClauses() {
		return Collections.unmodifiableList(complexClauses);
	}

	public Set<LiteralSet> getTransitiveStrongEdges() {
		return transitiveStrongEdges;
	}

	public void addClause(LiteralSet clause) {
		final int[] literals = clause.getLiterals();
		newLiteralsCheck: for (final int literal : literals) {
			for (int i = 0; i < adjList.size(); i++) {
				if (adjList.get(i).getVar() == literal) {
					continue newLiteralsCheck;
				}
			}
			addVertexForLiteral(literal);
		}
		switch (clause.size()) {
		case 0:
			throw new RuntimeContradictionException();
		case 1: {
			break;
		}
		case 2: {
			final Vertex vertex0 = getVertex(-literals[0]);
			final Vertex vertex1 = getVertex(-literals[1]);
			addStrongEdge(vertex0, -vertex1.getVar());
			addStrongEdge(vertex1, -vertex0.getVar());
			break;
		}
		default: {
			final int newClauseIndex = complexClauses.size();
			complexClauses.add(clause);
			for (final int literal : literals) {
				addWeakEdge(getVertex(-literal), newClauseIndex);
			}
			break;
		}
		}
	}

	private void addVertexForLiteral(int literal) {
		final Vertex negVertex = new Vertex(-Math.abs(literal));
		final Vertex posVertex = new Vertex(Math.abs(literal));

		negVertex.setCore(false);
		negVertex.setDead(false);
		posVertex.setCore(false);
		posVertex.setDead(false);

		negVertex.setStrongEdges(new int[0]);
		posVertex.setStrongEdges(new int[0]);

		negVertex.setComplexClauses(new int[0]);
		posVertex.setComplexClauses(new int[0]);

		negVertex.setId(adjList.size());
		adjList.add(negVertex);
		posVertex.setId(adjList.size());
		adjList.add(posVertex);
	}

	public void removeClause(LiteralSet clause) {
		final int[] literals = clause.getLiterals();
		if ((literals[0] == -460) && (literals[1] == 1115)) {
			System.out.println();
		}
		switch (clause.size()) {
		case 0:
			throw new RuntimeContradictionException();
		case 1: {
			break;
		}
		case 2: {
			final Vertex vertex0 = getVertex(-literals[0]);
			final Vertex vertex1 = getVertex(-literals[1]);
			removeStrongEdge(vertex0, -vertex1.getVar());
			removeStrongEdge(vertex1, -vertex0.getVar());
			break;
		}
		default: {
			int oldClauseIndex = -1;
			for (int i = 0; i < complexClauses.size(); i++) {
				if (complexClauses.get(i).containsAll(clause)) {
					oldClauseIndex = i;
					break;
				}
			}
			if (oldClauseIndex > -1) {
				for (final int literal : literals) {
					removeWeakEdge(getVertex(-literal), oldClauseIndex);
				}
				removeComplexClause(oldClauseIndex);
			}
			break;
		}
		}
	}

	private void removeComplexClause(int oldClauseIndex) {
		final List<LiteralSet> oldComplexClauses = getComplexClauses();
		final List<LiteralSet> newComplexClauses = new ArrayList<>(oldComplexClauses.size() - 1);
		boolean move = false;
		for (int i = 0; i < (oldComplexClauses.size() - 1); i++) {
			if (i == oldClauseIndex) {
				move = true;
			}
			if (move) {
				newComplexClauses.add(oldComplexClauses.get(i + 1));
			} else {
				newComplexClauses.add(oldComplexClauses.get(i));
			}
		}
		complexClauses.clear();
		complexClauses.addAll(newComplexClauses);
	}

	private void removeWeakEdge(Vertex vertex, int oldClauseIndex) {
		final int[] oldWeakEdges = vertex.getComplexClauses();
		boolean move = false;
		for (int i = 0; i < oldWeakEdges.length; i++) {
			if (oldWeakEdges[i] == oldClauseIndex) {
				move = true;
			}
			if (move && (i < (oldWeakEdges.length - 1))) {
				oldWeakEdges[i] = oldWeakEdges[i + 1];
			}
		}
		if (move) {
			final int[] newWeakEdges = new int[oldWeakEdges.length - 1];
			for (int i = 0; i < newWeakEdges.length; i++) {
				newWeakEdges[i] = oldWeakEdges[i];
			}
			vertex.setComplexClauses(newWeakEdges);
		}
	}

	private void removeStrongEdge(Vertex vertex, int edge) {
		final int[] tempNewStrongEdges = vertex.getStrongEdges().clone();
		boolean move = false;
		for (int i = 0; i < (tempNewStrongEdges.length); i++) {
			if (tempNewStrongEdges[i] == edge) {
				move = true;
			}
			if (move && (i < (tempNewStrongEdges.length - 1))) {
				tempNewStrongEdges[i] = tempNewStrongEdges[i + 1];
			}
		}
		if (move) {
			final int[] newStrongEdges = new int[tempNewStrongEdges.length - 1];
			for (int i = 0; i < newStrongEdges.length; i++) {
				newStrongEdges[i] = tempNewStrongEdges[i];
			}
			vertex.setStrongEdges(newStrongEdges);
		}
	}

	private void addWeakEdge(final Vertex vertex, final int index) {
		final int[] oldComplexClauses = vertex.getComplexClauses();
		final int[] newComplexClauses = Arrays.copyOf(oldComplexClauses, oldComplexClauses.length + 1);
		newComplexClauses[oldComplexClauses.length] = index;
		vertex.setComplexClauses(newComplexClauses);
	}

	private void addStrongEdge(final Vertex vertex, final int edge) {
		final int[] oldStrongEdges = vertex.getStrongEdges();
		for (int i = 0; i < oldStrongEdges.length; i++) {
			if (oldStrongEdges[i] == edge) {
				return;
			}
		}
		final int[] newStrongEdges = Arrays.copyOf(oldStrongEdges, oldStrongEdges.length + 1);
		newStrongEdges[oldStrongEdges.length] = edge;
		vertex.setStrongEdges(newStrongEdges);
	}

}
