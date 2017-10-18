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

import java.util.Collections;
import java.util.List;

/**
 * Handler to properly write / read objects.
 *
 * @author Sebastian Krieter
 */
public class FormatHandler<T> {

	private final IPersistentFormat<T> format;

	private List<Problem> lastWarnings = null;

	private T object;

	public FormatHandler(IPersistentFormat<T> format) {
		this(format, null);
	}

	public FormatHandler(IPersistentFormat<T> format, T object) {
		this.format = format;
		this.object = object;
	}

	public List<Problem> getLastWarnings() {
		return lastWarnings != null ? lastWarnings : Collections.<Problem> emptyList();
	}

	public T getObject() {
		return object;
	}

	public List<Problem> read(CharSequence source) {
		return lastWarnings = createFormat().read(object, source);
	}

	public void setObject(T object) {
		this.object = object;
	}

	public String write() {
		return createFormat().write(object);
	}

	protected IPersistentFormat<T> createFormat() {
		return format.getInstance();
	}

	public IPersistentFormat<T> getFormat() {
		return format;
	}

}
