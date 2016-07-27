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

import java.io.FileNotFoundException;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Capable of reading and writing a file in a certain format.
 * 
 * @see AFileManager
 * 
 * @author Sebastian Krieter
 */
public class SimpleFileHandler<T> {

	private static final Charset DEFAULT_CHARSET = Charset.forName("UTF-8");

	private IPersistentFormat<T> format;

	private final ProblemList lastProblems = new ProblemList();

	private T object;

	private Path path;

	public static <T> ProblemList load(Path path, T object, IPersistentFormat<T> format) {
		final SimpleFileHandler<T> fileHandler = new SimpleFileHandler<>(path, object, format);
		fileHandler.read();
		return fileHandler.getLastProblems();
	}

	public static <T> ProblemList save(Path path, T object, IPersistentFormat<T> format) {
		final SimpleFileHandler<T> fileHandler = new SimpleFileHandler<>(path, object, format);
		fileHandler.write();
		return fileHandler.getLastProblems();
	}
	
	public static <T> ProblemList convert(Path inPath, Path outPath, T object, IPersistentFormat<T> inFormat, IPersistentFormat<T> outFormat) {
		final SimpleFileHandler<T> fileHandler = new SimpleFileHandler<>(inPath, object, inFormat);
		ProblemList pl = new ProblemList();
		fileHandler.read();
		pl.addAll(fileHandler.getLastProblems());
		fileHandler.setPath(outPath);
		fileHandler.setFormat(outFormat);
		fileHandler.write();
		pl.addAll(fileHandler.getLastProblems());
		return pl;
	}
	
	public static <T> String saveToString(T object, IPersistentFormat<T> format) {
		return format.write(object);
	}
	
	public static <T> ProblemList loadFromString(String source, T object, IPersistentFormat<T> format) {
		return format.read(object, source);
	}

	public SimpleFileHandler(Path path, T object, IPersistentFormat<T> format) {
		this.format = format;
		this.path = path;
		this.object = object;
	}

	public IPersistentFormat<T> getFormat() {
		return format;
	}

	public ProblemList getLastProblems() {
		return lastProblems;
	}

	public T getObject() {
		return object;
	}

	public Path getPath() {
		return path;
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

	public boolean read() {
		lastProblems.clear();
		if (!Files.exists(path)) {
			lastProblems.add(new Problem(new FileNotFoundException(path.toString())));
			return false;
		}
		try {
			final T newObject = object;

			final String content = new String(FileSystem.read(path), DEFAULT_CHARSET);
			final List<Problem> problemList = format.getInstance().read(newObject, content);
			if (problemList != null) {
				lastProblems.addAll(problemList);
			}
		} catch (final Exception e) {
			handleException(e);
		}
		return !lastProblems.containsError();
	}

	public boolean write() {
		lastProblems.clear();
		try {
			final byte[] content = format.getInstance().write(object).getBytes(DEFAULT_CHARSET);
			FileSystem.write(path, content);
		} catch (final Exception e) {
			handleException(e);
		}
		return !lastProblems.containsError();
	}

	private void handleException(Exception e) {
		lastProblems.add(new Problem(e));
	}

}
