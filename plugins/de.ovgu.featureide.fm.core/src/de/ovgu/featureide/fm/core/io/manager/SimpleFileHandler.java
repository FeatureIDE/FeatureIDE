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

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import de.ovgu.featureide.fm.core.base.impl.FormatManager;
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

	private static final Charset DEFAULT_CHARSET;
	static {
		final Charset utf8 = Charset.forName("UTF-8");
		DEFAULT_CHARSET = utf8 != null ? utf8 : Charset.defaultCharset();
	}

	private IPersistentFormat<T> format;

	private final ProblemList problemList = new ProblemList();

	private T object;

	private Path path;

	/**
	 * Retrieves the file name of a {@link Path} without its extension.
	 *
	 * @param path the given path
	 * @return the file name
	 */
	public static String getFileName(Path path) {
		final String fileName = path.getFileName().toString();
		final int extensionIndex = fileName.lastIndexOf('.');
		return (extensionIndex > 0) ? fileName.substring(0, extensionIndex) : fileName;
	}

	public static <T> ProblemList load(Path path, T object, IPersistentFormat<T> format) {
		final SimpleFileHandler<T> fileHandler = new SimpleFileHandler<>(path, object, format);
		fileHandler.read();
		return fileHandler.getLastProblems();
	}

	public static <T> ProblemList load(InputStream inputStream, T object, IPersistentFormat<T> format) {
		final SimpleFileHandler<T> fileHandler = new SimpleFileHandler<>(null, object, format);
		fileHandler.read(inputStream);
		return fileHandler.getLastProblems();
	}

	public static <T> ProblemList load(Path path, T object, FormatManager<? extends IPersistentFormat<T>> formatManager) {
		return load(new SimpleFileHandler<>(path, object, null), formatManager);
	}

	public static <T> ProblemList load(SimpleFileHandler<T> fileHandler, FormatManager<? extends IPersistentFormat<T>> formatManager) {
		final String content = fileHandler.getContent();

		if (content != null) {
			final String fileName = fileHandler.getPath().getFileName().toString();
			final IPersistentFormat<T> format = formatManager.getFormatByContent(content, fileName);
			if (format == null) {
				fileHandler.getLastProblems().add(new Problem(new FormatManager.NoSuchExtensionException("No format found for file \"" + fileName + "\"!")));
			} else {
				fileHandler.setFormat(format);
				fileHandler.parse(content);
			}
		}
		return fileHandler.getLastProblems();
	}

	public static <T> ProblemList save(Path path, T object, IPersistentFormat<T> format) {
		final SimpleFileHandler<T> fileHandler = new SimpleFileHandler<>(path, object, format);
		fileHandler.write();
		return fileHandler.getLastProblems();
	}

	public static <T> ProblemList convert(Path inPath, Path outPath, T object, IPersistentFormat<T> inFormat, IPersistentFormat<T> outFormat) {
		final SimpleFileHandler<T> fileHandler = new SimpleFileHandler<>(inPath, object, inFormat);
		final ProblemList pl = new ProblemList();
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
		return problemList;
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
		problemList.clear();
		return parse(getContent());
	}

	public boolean read(InputStream inputStream) {
		problemList.clear();
		return parse(getContent(inputStream));
	}

	String getContent() {
		if (!Files.exists(path)) {
			problemList.add(new Problem(new FileNotFoundException(path.toString())));
			return null;
		}

		try {
			return new String(FileSystem.read(path), DEFAULT_CHARSET);
		} catch (final Exception e) {
			problemList.add(new Problem(e));
			return null;
		}
	}

	private String getContent(InputStream inputStream) {
		try {
			final StringBuilder sb = new StringBuilder();
			try (BufferedReader br = new BufferedReader(new InputStreamReader(inputStream, DEFAULT_CHARSET))) {
				for (String line; (line = br.readLine()) != null;) {
					sb.append(line);
					sb.append(System.lineSeparator());
				}
			}
			return sb.toString();
		} catch (final Exception e) {
			problemList.add(new Problem(e));
			return null;
		}
	}

	boolean parse(String content) {
		if (content != null) {
			try {
				final List<Problem> parsingProblemList = format.getInstance().read(object, content);
				if (problemList != null) {
					problemList.addAll(parsingProblemList);
				}
			} catch (final Exception e) {
				problemList.add(new Problem(e));
			}
		}

		return !problemList.containsError();
	}

	public boolean write() {
		problemList.clear();
		try {
			final byte[] content = format.getInstance().write(object).getBytes(DEFAULT_CHARSET);
			FileSystem.write(path, content);
		} catch (final Exception e) {
			problemList.add(new Problem(e));
		}

		return !problemList.containsError();
	}

}
