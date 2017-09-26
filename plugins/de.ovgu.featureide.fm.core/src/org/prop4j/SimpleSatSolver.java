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
package org.prop4j;

import java.util.List;

import org.sat4j.core.VecInt;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Logger;

/**
 *
 * @author Sebastian Krieter
 */
public class SimpleSatSolver extends SatSolver {

	final byte[] b;

	private IVecInt backbone = new VecInt();

	private int[] model;

	private boolean satisfiable = false;

	public SimpleSatSolver(Node node, long timeout) {
		super(node, timeout);
		b = new byte[solver.nVars()];
	}

	public void setBackbone(List<Literal> knownLiterals, Literal curLiteral) {
		backbone = new VecInt((knownLiterals.size() + 1) << 1);
		for (final Literal node : knownLiterals) {
			backbone.push(getIntOfLiteral(node));
		}
		final int x = getIntOfLiteral(curLiteral);

		backbone.push(x);
		try {
			satisfiable = solver.isSatisfiable(backbone);
		} catch (final TimeoutException e) {
			Logger.logError(e);
		}
		if (satisfiable) {
			model = solver.model();
			for (int i = 0; i < model.length; i++) {
				b[i] = (byte) Math.signum(model[i]);
			}
			assert model.length == b.length : "Short Model Length";
		} else {
			throw new RuntimeException("Contradiction");
		}
	}

	public byte getValueOf(Literal literal) {
		if (satisfiable) {
			final int i = getIntOfLiteral(literal) - 1;
			if (b[i] != 0) {
				final int x = model[i];
				backbone.push(-x);
				try {
					if (solver.isSatisfiable(backbone)) {
						backbone.pop();
						final int[] tempModel = solver.model();
						for (int j = 0; j < tempModel.length; j++) { // i + 1
							if (b[j] != (byte) Math.signum(tempModel[j])) {
								b[j] = 0;
							}
						}
					} else {
						backbone.pop().push(x);
						return (byte) Math.signum(x);
					}
				} catch (final TimeoutException e) {
					Logger.logError(e);
					backbone.pop();
				}
			}
		}
		return 0;
	}

}
