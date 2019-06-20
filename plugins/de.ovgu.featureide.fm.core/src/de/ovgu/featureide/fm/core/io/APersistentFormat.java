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
package de.ovgu.featureide.fm.core.io;

/**
 * Reads / Writes a feature order file.
 *
 * @author Sebastian Krieter
 */
public abstract class APersistentFormat<T> implements IPersistentFormat<T> {

	@Override
	public APersistentFormat<T> getInstance() {
		return this;
	}

	@Override
	public ProblemList read(T object, CharSequence source) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String write(T object) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean supportsRead() {
		return false;
	}

	@Override
	public boolean supportsWrite() {
		return false;
	}

	@Override
	public boolean supportsContent(CharSequence content) {
		return supportsRead();
	}

	@Override
	public boolean supportsContent(LazyReader reader) {
		return supportsRead();
	}

	@Override
	public boolean initExtension() {
		return true;
	}

}
