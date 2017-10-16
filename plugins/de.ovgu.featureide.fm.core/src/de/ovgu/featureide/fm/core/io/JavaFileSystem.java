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
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;

import de.ovgu.featureide.fm.core.io.FileSystem.IFileSystem;

public class JavaFileSystem implements IFileSystem {

	@Override
	public void write(Path path, byte[] content) throws IOException {
		Files.write(path, content, StandardOpenOption.TRUNCATE_EXISTING, StandardOpenOption.CREATE, StandardOpenOption.WRITE);
	}

	@Override
	public void append(Path path, byte[] content) throws IOException {
		Files.write(path, content, StandardOpenOption.APPEND, StandardOpenOption.CREATE, StandardOpenOption.WRITE);
	}

	@Override
	public byte[] read(Path path) throws IOException {
		return Files.readAllBytes(path);
	}

	@Override
	public void mkDir(Path path) throws IOException {
		Files.createDirectories(path);
	}

	@Override
	public void delete(Path path) throws IOException {
		Files.deleteIfExists(path);
	}

	@Override
	public boolean exists(Path path) {
		return Files.exists(path);
	}

}
