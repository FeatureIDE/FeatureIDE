/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.FileVisitResult;
import java.nio.file.FileVisitor;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.BasicFileAttributes;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.sxfm.SXFMReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;

/**
 * 
 * @author Sebastian Krieter
 */
public class FMConverter {

	public static enum Format {
		SXFM, FIDE
	}
	
	public static boolean convert(final Path inputPath, final Path outputPath, Format inputFormat, Format outputFormat) {
		final AbstractFeatureModelReader reader;
		final AbstractFeatureModelWriter writer;
		final FeatureModel featureModel = new FeatureModel();
		switch (inputFormat) {
		case SXFM:
			reader = new SXFMReader(featureModel);
			break;
		default:
			return false;
		}
		switch (outputFormat) {
		case FIDE:
			writer = new XmlFeatureModelWriter(featureModel);
			break;
		default:
			return false;
		}
		
		
		try {
			Files.walkFileTree(inputPath.toAbsolutePath(), new FileVisitor<Path>() {
				@Override
				public FileVisitResult postVisitDirectory(Path arg0, IOException arg1) throws IOException {
					return FileVisitResult.CONTINUE;
				}
				
				@Override
				public FileVisitResult preVisitDirectory(Path arg0, BasicFileAttributes arg1) throws IOException {
					return FileVisitResult.CONTINUE;
				}

				@Override
				public FileVisitResult visitFile(Path arg0, BasicFileAttributes arg1) throws IOException {
					final Path fileName = arg0.getFileName();
					if (arg1.isRegularFile() && fileName != null) {
						try {
							reader.readFromFile(arg0.toFile());
						} catch (FileNotFoundException | UnsupportedModelException e) {
						}
						final Path outputFile = outputPath.resolve(inputPath.relativize(arg0));
						Files.createDirectories(outputFile.getRoot().resolve(outputFile.subpath(0, outputFile.getNameCount() - 1)));
						Files.deleteIfExists(outputFile);
						writer.writeToFile(outputFile.toFile());
					}
					return FileVisitResult.CONTINUE;
				}

				@Override
				public FileVisitResult visitFileFailed(Path arg0, IOException arg1) throws IOException {
					return FileVisitResult.CONTINUE;
				}
			});
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return true;
	}
}
