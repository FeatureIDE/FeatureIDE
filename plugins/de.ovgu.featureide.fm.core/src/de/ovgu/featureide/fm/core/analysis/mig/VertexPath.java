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

public class VertexPath implements Visitor<Void>, Serializable {

	private static final long serialVersionUID = -4537177543155207865L;

	private static final int numberBits = Long.SIZE >> 1;

	private final ModalImplicationGraph mig;
	private final int vertexId;

	private final long[] path;

	public VertexPath(ModalImplicationGraph mig, int id, int numberVertex) {
		this.mig = mig;
		vertexId = id;
		path = new long[numberVertex / numberBits];
	}

	public int getId() {
		return vertexId;
	}

	public static final long MASK = 0b11;
	public static final long BIT_STRONG = 0b11;
	public static final long BIT_WEAK = 0b10;
	public static final long BIT_NOPATH = 0b01;
	public static final long BIT_UNKNOWN = 0b00;

	public static boolean isPath(long value) {
		return (value & BIT_WEAK) == BIT_WEAK;
	}

	public static boolean isWeakPath(long value) {
		return value == BIT_WEAK;
	}

	public static boolean isStrongPath(long value) {
		return value == BIT_STRONG;
	}

	public static boolean isNoPath(long value) {
		return value == BIT_NOPATH;
	}

	public static boolean isUnknown(long value) {
		return value == BIT_UNKNOWN;
	}

	public boolean hasPath(int id) {
		return isPath(getValue(id));
	}

	public boolean hasWeakPath(int id) {
		return isWeakPath(getValue(id));
	}

	public boolean hasStrongPath(int id) {
		return isStrongPath(getValue(id));
	}

	public boolean hasNoPath(int id) {
		return isNoPath(getValue(id));
	}

	public boolean hasUnknown(int id) {
		return isUnknown(getValue(id));
	}

	public long getValue(int id) {
		final int x = id / numberBits;
		final int y = (id % numberBits) << 1;
		return (path[x] >> y) & MASK;
	}

	public void setValue(int id, long value) {
		final int x = id / numberBits;
		final int y = (id % numberBits) << 1;
		path[x] = (path[x] & (~(MASK << y))) | (value << y);
	}

	@Override
	public VisitResult visitStrong(int literal) {
		setValue(mig.getVertex(literal).getId(), BIT_STRONG);
		return VisitResult.Continue;
	}

	@Override
	public VisitResult visitWeak(int literal) {
		setValue(mig.getVertex(literal).getId(), BIT_WEAK);
		return VisitResult.Continue;
	}

	@Override
	public Void getResult() {
		return null;
	}

}
