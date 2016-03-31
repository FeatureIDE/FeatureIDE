/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;

/**
 * Capable of reading a file in a certain format.</br>
 * <b>Intended for read-only access of files!</b></br>
 * For changing a file's content use the specific subclass of {@link AFileManager} via {@link FileManagerMap}.
 * 
 * @see FileWriter
 * 
 * @author Sebastian Krieter
 */
public class FileReader<T> {

	private final List<Problem> lastProblems = new LinkedList<>();

	private IPersistentFormat<T> format;

	private Path path;

	private T object;

	public FileReader() {
		this.format = null;
		this.path = null;
		this.object = null;
	}

	public FileReader(T object) {
		this.object = object;
		this.format = null;
		this.path = null;
	}

	public FileReader(Path path, T object, IPersistentFormat<T> format) {
		this.format = format;
		this.path = path;
		this.object = object;
	}

	public FileReader(String path, T object, IPersistentFormat<T> format) {
		this(Paths.get(path), object, format);
	}

	public List<Problem> getLastProblems() {
		return lastProblems;
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

	public boolean read() {
		if (!Files.exists(path)) {
			return false;
		}
		lastProblems.clear();
		try {
			final T newObject = object;

			final String content = new String(Files.readAllBytes(path), Charset.availableCharsets().get("UTF-8"));
			List<Problem> problemList = format.getInstance().read(newObject, content);
			if (problemList != null) {
				lastProblems.addAll(problemList);
			}
		} catch (Exception e) {
			handleException(e);
		}
		return lastProblems.isEmpty();
	}

	private void handleException(Exception e) {
		lastProblems.add(new Problem(e));
		FMCorePlugin.getDefault().logError(e);
	}

	public void setFormat(IPersistentFormat<T> format) {
		this.format = format;
	}

	public void setObject(T object) {
		this.object = object;
	}

	public void setPath(Path path) {
		this.path = path;
	}

	public IPersistentFormat<T> getFormat() {
		return format;
	}

	public T getObject() {
		return object;
	}

	public Path getPath() {
		return path;
	}

}
