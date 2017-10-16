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
package de.ovgu.featureide.fm.core.analysis.cnf.generator;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.CoreDeadAnalysis;
import de.ovgu.featureide.fm.core.base.IModalImplicationGraph;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * Adjacency list implementation for a feature graph.
 *
 * @author Sebastian Krieter
 */
public class ModalImplicationGraph implements IModalImplicationGraph {

	private static final long serialVersionUID = 5258868675944962032L;

	public static class Vertex implements Serializable {

		private static final long serialVersionUID = -3218194304764541434L;

		public final byte core;
		public final int id;
		public final int[] negComplexClauses;
		public int[] negStrongEdges;

		public final int[] posComplexClauses;
		public int[] posStrongEdges;

		public Vertex(byte core, int id, int[] posStrongEdges, int[] negStrongEdges, int[] posComplexClauses, int[] negComplexClauses) {
			this.core = core;
			this.id = id;
			this.posStrongEdges = posStrongEdges;
			this.negStrongEdges = negStrongEdges;
			this.posComplexClauses = posComplexClauses;
			this.negComplexClauses = negComplexClauses;
		}

		public byte getCore() {
			return core;
		}

		public int getId() {
			return id;
		}

		public int[] getNegComplexClauses() {
			return negComplexClauses;
		}

		public int[] getNegStrongEdges() {
			return negStrongEdges;
		}

		public int[] getPosComplexClauses() {
			return posComplexClauses;
		}

		public int[] getPosStrongEdges() {
			return posStrongEdges;
		}

	}

	final List<Vertex> adjList;

	final List<LiteralSet> complexClauses = new ArrayList<>(0);

	boolean[] complete;

	public ModalImplicationGraph() {
		adjList = new ArrayList<>(0);
		complete = null;
	}

	public ModalImplicationGraph(int numVariables) {
		adjList = new ArrayList<>(numVariables);
		complete = new boolean[numVariables];
	}

	public void copyValues(ModalImplicationGraph other) {
		adjList.addAll(other.adjList);
		complexClauses.addAll(other.complexClauses);
		complete = Arrays.copyOf(other.complete, other.complete.length);
	}

	@Override
	public boolean isStrongPath(int startLiteral, int endLiteral) {
		if (startLiteral != endLiteral) {
			final Vertex vertex = adjList.get(Math.abs(startLiteral) - 1);
			final int[] strongEdges = (startLiteral < 0) ? vertex.negStrongEdges : vertex.posStrongEdges;
			for (int i = 0; i < strongEdges.length; i++) {
				if (strongEdges[i] == endLiteral) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public boolean isComplete(int startLiteral) {
		return complete[Math.abs(startLiteral) - 1];
	}

	@Override
	public void complete(int startLiteral) {
		final int startIndex = Math.abs(startLiteral) - 1;
		synchronized (complete) {
			if (!complete[startIndex]) {
				final LiteralSet weaklyConnected = new Traverser(this).getWeaklyConnected(startLiteral);
				final CoreDeadAnalysis analysis = new CoreDeadAnalysis(new CNF(complexClauses), weaklyConnected);
				analysis.setAssumptions(new LiteralSet(startLiteral));
				final LiteralSet stronglyConnected = LongRunningWrapper.runMethod(analysis);

				if (startLiteral > 0) {
					adjList.get(startIndex).posStrongEdges = stronglyConnected.getLiterals();
				} else {
					adjList.get(startIndex).posStrongEdges = stronglyConnected.getLiterals();
				}

				complete[startIndex] = true;
			}
		}
	}

	public List<Vertex> getAdjList() {
		return Collections.unmodifiableList(adjList);
	}

	public List<LiteralSet> getComplexClauses() {
		return complexClauses;
	}

}
