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
