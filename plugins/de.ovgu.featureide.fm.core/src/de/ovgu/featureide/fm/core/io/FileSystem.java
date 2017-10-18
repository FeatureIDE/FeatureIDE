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

import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.file.Path;

/**
 *
 * @author Sebastian Krieter
 */
public final class FileSystem {

	public static interface IFileSystem {

		void write(Path path, byte[] content) throws IOException;

		void append(Path path, byte[] content) throws IOException;

		byte[] read(Path path) throws IOException;

		void mkDir(Path path) throws IOException;

		void delete(Path path) throws IOException;

		boolean exists(Path path);
	}

	public static IFileSystem INSTANCE = new JavaFileSystem();

	public static void append(Path path, byte[] content) throws IOException {
		INSTANCE.append(path, content);
	}

	public static void write(Path path, byte[] content) throws IOException {
		INSTANCE.write(path, content);
	}

	public static byte[] read(Path path) throws IOException {
		return INSTANCE.read(path);
	}

	public static void mkDir(Path path) throws IOException {
		INSTANCE.mkDir(path);
	}

	public static void delete(Path path) throws IOException {
		INSTANCE.delete(path);
	}

	public static boolean exists(Path path) {
		return INSTANCE.exists(path);
	}

	public static void write(Path path, String content) throws IOException {
		INSTANCE.write(path, content.getBytes(Charset.forName("UTF-8")));
	}

	public static String readtoString(Path path) throws IOException {
		return new String(INSTANCE.read(path), Charset.forName("UTF-8"));
	}

	private FileSystem() {}

}
