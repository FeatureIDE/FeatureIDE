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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.AdvancedSatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISimpleSatSolver.SatResult;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationTester {

	private final int t;
	private final CNF cnf;
	private final LiteralSet[] nodeArray;
	private final ISatSolver solver;
	private final List<int[]> configurations;

	public TWiseConfigurationTester(CNF cnf, int t, LiteralSet[] nodeArray, List<int[]> configurations) {
		this.cnf = cnf;
		this.t = t;
		this.nodeArray = nodeArray;
		this.configurations = configurations;
		if (!this.cnf.getClauses().isEmpty()) {
			solver = new AdvancedSatSolver(this.cnf);
		} else {
			solver = null;
		}
	}

	public void test() {
		System.out.println("Testing results...");
		if (solver != null) {
			System.out.print("\tTesting configuration validity...");
			final int c = 0;
			for (final int[] is : configurations) {
				int length = is.length;
				for (int i = 0; i < length; i++) {
					if (is[i] == 0) {
						is[i] = is[--length];
						i--;
					}
				}
				final SatResult hasSolution = solver.hasSolution(Arrays.copyOf(is, length));
				switch (hasSolution) {
				case FALSE:
					System.out.println(" FAIL");
					throw new RuntimeException("Invalid configuration.");
				case TIMEOUT:
					System.err.println("Timeout! " + c);
					break;
				case TRUE:
					break;
				default:
					throw new AssertionError();
				}
			}
			System.out.println(" PASS");
		}

		System.out.print("\tTesting combination completeness...");
		comboLoop: for (final Iterator<int[]> iterator = new LexicographicIterator(t, nodeArray.length); iterator.hasNext();) {
			final int[] indexArray = iterator.next();
			if (indexArray == null) {
				break;
			}

			for (int i = 0; i < indexArray.length; i++) {
				final LiteralSet literalsI = nodeArray[indexArray[i]];
				for (int j = i + 1; j < indexArray.length; j++) {
					final LiteralSet literalsJ = nodeArray[indexArray[j]];
					if (literalsI.countConflicts(literalsJ) != 0) {
						continue comboLoop;
					}
				}
			}

			configurationLoop: for (final int[] solution : configurations) {
				for (final int i : indexArray) {
					for (final int literal : nodeArray[i].getLiterals()) {
						if (solution[Math.abs(literal) - 1] == -literal) {
							continue configurationLoop;
						}
					}
				}
				continue comboLoop;
			}

			if (solver != null) {
				for (int i = 0; i < t; i++) {
					solver.assignmentPushAll(nodeArray[indexArray[i]].getLiterals());
				}
				final SatResult hasSolution = solver.hasSolution();
				switch (hasSolution) {
				case FALSE:
					solver.assignmentClear(0);
					continue comboLoop;
				case TIMEOUT:
					System.err.println("Timeout!");
					solver.assignmentClear(0);
					continue comboLoop;
				case TRUE:
					break;
				default:
					throw new AssertionError();
				}
			}
			System.out.println(" FAIL");
			throw new RuntimeException("Uncovered combination.");
		}
		System.out.println(" PASS");
	}

}
