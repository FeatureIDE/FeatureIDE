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
