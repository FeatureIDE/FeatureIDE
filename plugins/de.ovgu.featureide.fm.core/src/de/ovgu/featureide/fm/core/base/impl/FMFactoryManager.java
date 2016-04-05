/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base.impl;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;

/**
 * Returns custom factories to create {@link IFeatureModel}, {@link IFeature}, and {@link IConstraint} instances.
 * 
 * @author Sebastian Krieter
 */
public final class FMFactoryManager {

	private FMFactoryManager() {
	}

	private final static IFeatureModelFactory[] factoryArray;
	static {
		factoryArray = new IFeatureModelFactory[2];
		factoryArray[0] = DefaultFeatureModelFactory.getInstance();
		factoryArray[1] = ExtendedFeatureModelFactory.getInstance();
	}

	/**
	 * @return Returns the default instance of the built-in {@link DefaultFeatureModelFactory} which provides access to the default {@link IFeatureModel} and
	 *         {@link IFeature} implementations of FeatureIDE
	 */
	public static IFeatureModelFactory getFactory() {
		return DefaultFeatureModelFactory.getInstance();
	}

	/**
	 * Returns a specific factory associated with the string <b>id</b>. By default, the following
	 * factories are available:
	 * <ul>
	 * <li><b>de.ovgu.featureide.fm.core.DefaultFeatureModelFactory</b>: An instance of {@link DefaultFeatureModelFactory}</li>
	 * <li><b>de.ovgu.featureide.fm.core.ExtendedFeatureModelFactory</b>: An instance of {@link ExtendedFeatureModelFactory}</li>
	 * </ul>
	 * @param id the (unique) identifier for an instance of {@link IFeatureModelFactory} to be returned
	 * @return Returns Instance of feature model factory associated with <b>id</b>, or throws <b<>RuntimeException</b> in case <b>id</b> is not known
	 */
	public static IFeatureModelFactory getFactory(String id) {
		for (IFeatureModelFactory factory : factoryArray) {
			if (factory.getId().equals(id)) {
				return factory;
			}
		}
		throw new RuntimeException("No factory found for ID " + id);
	}

}
