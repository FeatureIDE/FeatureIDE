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
package de.ovgu.featureide.fm.core.io.manager;

import java.nio.file.Path;

import de.ovgu.featureide.fm.core.io.IPersistentFormat;

/**
 * Based on {@link SimpleFileHandler}. Provides convenient methods for reading / writing files with a certain {@link IPersistentFormat format}.
 *
 * @see AFileManager
 *
 * @author Sebastian Krieter
 */
public class FileHandler<T> extends SimpleFileHandler<T> {

	public FileHandler() {
		this(null, null, null);
	}

	public FileHandler(IPersistentFormat<T> format) {
		this(null, null, format);
	}

	public FileHandler(Path path) {
		this(path, null, null);
	}

	public FileHandler(Path path, IPersistentFormat<T> format) {
		this(path, null, format);
	}

	public FileHandler(Path path, T object) {
		this(path, object, null);
	}

	public FileHandler(Path path, T object, IPersistentFormat<T> format) {
		super(path, object, format);
	}

	public FileHandler(T object) {
		this(null, object, null);
	}

	public FileHandler(T object, IPersistentFormat<T> format) {
		this(null, object, format);
	}

	public boolean read(Path path) {
		setPath(path);
		return read();
	}

	public boolean read(Path path, IPersistentFormat<T> format) {
		setPath(path);
		setFormat(format);
		return read();
	}

	public boolean read(Path path, T object) {
		setPath(path);
		setObject(object);
		return read();
	}

	public boolean read(Path path, T object, IPersistentFormat<T> format) {
		setPath(path);
		setObject(object);
		setFormat(format);
		return read();
	}

	public boolean write(Path path) {
		setPath(path);
		return write();
	}

	public boolean write(Path path, IPersistentFormat<T> format) {
		setPath(path);
		setFormat(format);
		return write();
	}

	public boolean write(Path path, T object) {
		setPath(path);
		setObject(object);
		return write();
	}

	public boolean write(Path path, T object, IPersistentFormat<T> format) {
		setPath(path);
		setObject(object);
		setFormat(format);
		return write();
	}

}
