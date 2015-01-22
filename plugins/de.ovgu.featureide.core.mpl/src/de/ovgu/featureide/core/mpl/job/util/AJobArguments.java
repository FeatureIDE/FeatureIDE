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
package de.ovgu.featureide.core.mpl.job.util;

import java.lang.reflect.Constructor;

import de.ovgu.featureide.core.mpl.MPLPlugin;

public abstract class AJobArguments {
	
	private final Constructor<? extends IChainJob> constructor;
	
	@SuppressWarnings("unchecked")
	protected AJobArguments(Class<? extends AJobArguments> cl) {
		Constructor<? extends IChainJob> temp;
		try {
			temp = (Constructor<? extends IChainJob>) cl.getEnclosingClass().getDeclaredConstructor(cl);
			temp.setAccessible(true);
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			temp = null;
		}
		constructor = temp;
	}
	
	public IChainJob createJob() {
		if (constructor == null) {
			return null;
		}
		try {
			return constructor.newInstance(this);
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
			return null;
		}
	}
}
