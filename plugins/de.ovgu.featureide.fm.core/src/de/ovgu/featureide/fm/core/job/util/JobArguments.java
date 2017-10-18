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
package de.ovgu.featureide.fm.core.job.util;

import java.lang.reflect.Constructor;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;

/**
 * This class is implemented by callers as an anonymous class to encapsulate parameters for the job constructor, so multiple {@code Job}s can be called with low
 * effort.
 *
 * @author Sebastian Krieter
 */
public abstract class JobArguments {

	private final Constructor<? extends LongRunningMethod<?>> constructor;

	@SuppressWarnings("unchecked")
	protected JobArguments(Class<? extends JobArguments> cl) {
		Constructor<? extends LongRunningMethod<?>> tempConstructor;
		try {
			tempConstructor = (Constructor<? extends LongRunningMethod<?>>) cl.getEnclosingClass().getDeclaredConstructor(cl);
			tempConstructor.setAccessible(true);
		} catch (final Exception e) {
			Logger.logError(e);
			tempConstructor = null;
		}
		constructor = tempConstructor;
	}

	public LongRunningMethod<?> createJob() {
		if (constructor == null) {
			return null;
		}
		try {
			return constructor.newInstance(this);
		} catch (final Exception e) {
			Logger.logError(e);
			return null;
		}
	}
}
