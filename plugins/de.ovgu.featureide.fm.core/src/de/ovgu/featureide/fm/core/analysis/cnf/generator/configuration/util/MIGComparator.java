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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util;

import java.util.Comparator;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.mig.ModalImplicationGraph;
import de.ovgu.featureide.fm.core.analysis.mig.Vertex;

public class MIGComparator implements Comparator<LiteralSet> {

	private static class VertexInfo {

		int weakOut, weakIn, strongOut, strongIn;

		@Override
		public String toString() {
			return "VertexInfo [weakOut=" + weakOut + ", weakIn=" + weakIn + ", strongOut=" + strongOut + ", strongIn=" + strongIn + "]";
		}
	}

	private final ModalImplicationGraph mig;
	private final VertexInfo[] vertexInfos;

	public MIGComparator(ModalImplicationGraph mig) {
		this.mig = mig;
		vertexInfos = new VertexInfo[mig.getAdjList().size()];
		for (final Vertex vertex : mig.getAdjList()) {
			vertexInfos[vertex.getId()] = new VertexInfo();
		}
		for (final Vertex vertex : mig.getAdjList()) {
			final VertexInfo vertexInfo = vertexInfos[vertex.getId()];
			vertexInfo.strongOut = vertex.getStrongEdges().length;
			vertexInfo.weakOut = vertex.getComplexClauses().length;
			for (final int strongEdge : vertex.getStrongEdges()) {
				vertexInfos[mig.getVertex(strongEdge).getId()].strongIn++;
			}
			for (final int complexClauseIndex : vertex.getComplexClauses()) {
				final LiteralSet literalSet = mig.getComplexClauses().get(complexClauseIndex);
				for (final int literal : literalSet.getLiterals()) {
					if (literal != vertex.getVar()) {
						vertexInfos[mig.getVertex(literal).getId()].weakIn++;
					}
				}
			}
		}
	}

	@Override
	public int compare(LiteralSet o1, LiteralSet o2) {
		final double f1 = computeValue(o1);
		final double f2 = computeValue(o2);
		return (int) Math.signum(f1 - f2);
	}

	public String getValue(LiteralSet o1) {
		final VertexInfo vi1 = vertexInfos[mig.getVertex(o1.getLiterals()[0]).getId()];
		final double f1 = computeValue(o1);
		return o1 + " | " + vi1 + " -> " + f1;
	}

	public double computeValue(LiteralSet... set) {
		int vIn = 0;
		int vOut = 0;
		for (final LiteralSet literalSet : set) {
			for (final int literal : literalSet.getLiterals()) {
				final VertexInfo info = vertexInfos[mig.getVertex(literal).getId()];
				vIn += (info.strongIn) + info.weakIn;
				vOut += (info.strongOut) + info.weakOut;
			}
		}
		return (double) (vIn - (vOut * vOut));
	}

	public int getOut(LiteralSet... set) {
		int vOut = 0;
		for (final LiteralSet literalSet : set) {
			for (final int literal : literalSet.getLiterals()) {
				final VertexInfo info = vertexInfos[mig.getVertex(literal).getId()];
				vOut += info.strongOut + info.weakOut;
			}
		}
		return vOut;
	}

}
