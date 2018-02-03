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
package org.prop4j.solver.impl;

import java.util.Arrays;

/**
 * Static class used to provide some basic functionality that can be used with any kind of solver.
 *
 * @author Joshua Sprey
 */
public class SolverUtils {

	/**
	 * Convert some solution models to Sat4J format. Input is an array of Objects which should be Integer. If one Object is not an Integer the method will
	 * return null;
	 *
	 * @param model inputModel as Object array containing only Integers
	 * @return int[] when model is only containing Integer objects
	 */
	public static int[] getIntModel(Object[] model) {
		final int[] intModel = new int[model.length];
		for (int i = 0; i < model.length; i++) {
			if (model[i] instanceof Integer) {
				intModel[i] = (Integer) model[i];
			} else {
				return null;
			}
		}
		return intModel;
	}

	/**
	 * Converts a int array to an Object array
	 *
	 * @param model
	 * @return
	 */
	public static Object[] getObjectModel(int[] model) {
		final Object[] objectModel = new Object[model.length];
		for (int i = 0; i < model.length; i++) {
			objectModel[i] = new Integer(model[i]);
		}
		return objectModel;
	}

	public static void updateModel(final int[] model1, int[] model2) {
		for (int i = 0; i < model1.length; i++) {
			final int x = model1[i];
			final int y = model2[i];
			if (x != y) {
				model1[i] = 0;
			}
		}
	}

	public static void updateModel(final int[] model1, Iterable<int[]> models) {
		for (int i = 0; i < model1.length; i++) {
			final int x = model1[i];
			for (final int[] model2 : models) {
				final int y = model2[i];
				if (x != y) {
					model1[i] = 0;
					break;
				}
			}
		}
	}

	public static int[] negateModel(int[] ar) {
		final int[] nar = Arrays.copyOf(ar, ar.length);
		for (int i = 0; i < nar.length; i++) {
			nar[i] = -nar[i];
		}
		return nar;
	}
}
