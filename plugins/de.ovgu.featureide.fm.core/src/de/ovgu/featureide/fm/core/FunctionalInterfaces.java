/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core;

/**
 * Common interfaces for functional style.
 * 
 * @author Marcus Pinnecke
 */
public abstract class FunctionalInterfaces {
	
	public static interface IFunction<T,U> {
		U invoke(T t);
	}
	
	public static interface IBinaryFunction<T,U,R> {
		R invoke(T t, U u);
	}
	
	public static class IdentityFunction<T> implements IFunction<T, T> {
		@Override
		public T invoke(T t) {
			return t;
		}
	};
	
	public static interface IConsumer<T> {
		void invoke(T t);
	}
	
	public static interface IProvider<T> {
		T invoke();
	}
	
	public static class NullFunction<T, U> implements IFunction<T, U> {
		@Override
		public U invoke(T t) {
			return null;
		}
	};

}
