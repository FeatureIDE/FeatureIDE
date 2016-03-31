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
import java.nio.file.StandardOpenOption;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;

/**
 * Capable of saving a file in a certain format.</br>
 * <b>Intended for export purposes only!</b></br>
 * For normal reading/writing a file use the specific subclass of {@link AFileManager}.
 * 
 * @see FileReader
 * 
 * @author Sebastian Krieter
 */
public class FileWriter<T> {

	private final List<Problem> lastProblems = new LinkedList<>();

	private IPersistentFormat<T> format;

	private Path path;

	private T object;

	public FileWriter() {
		this.format = null;
		this.path = null;
		this.object = null;
	}

	public FileWriter(IPersistentFormat<T> format) {
		this.format = format;
		this.path = null;
		this.object = null;
	}

	public FileWriter(T object) {
		this.format = null;
		this.path = null;
		this.object = object;
	}

	public FileWriter(T object, IPersistentFormat<T> format) {
		this.format = format;
		this.path = null;
		this.object = object;
	}

	public FileWriter(Path path, T object, IPersistentFormat<T> format) {
		this.format = format;
		this.path = path;
		this.object = object;
	}

	public FileWriter(String path, T object, IPersistentFormat<T> format) {
		this(Paths.get(path), object, format);
	}

	public List<Problem> getLastProblems() {
		return lastProblems;
	}

	public boolean save() {
		lastProblems.clear();
		try {
			final byte[] content = format.getInstance().write(object).getBytes(Charset.availableCharsets().get("UTF-8"));
			Files.write(path, content, StandardOpenOption.TRUNCATE_EXISTING, StandardOpenOption.CREATE, StandardOpenOption.WRITE);
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
