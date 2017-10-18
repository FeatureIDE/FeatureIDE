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

import java.io.File;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.List;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * This Wrapper makes it possible, to read feature models from IFiles, e.g. if working with Eclipse plugins Otherwise only the classes extending
 * {@link AbstractFeatureModelReader} are needed
 *
 * @deprecated Use {@link IFeatureModelFormat} and {@link FileHandler} instead. <br/> {@link IFile} can be converted via
 *             {@code Paths.getPath(ifile.getLocationURI())}.
 *
 * @author Sönke Holthusen
 * @author Marcus Pinnecke (Feature Interface)
 */
@Deprecated
public class FeatureModelReaderIFileWrapper extends AbstractFeatureModelReader {

	private final AbstractFeatureModelReader reader;

	public FeatureModelReaderIFileWrapper(AbstractFeatureModelReader reader) {
		this.reader = reader;
	}

	@Override
	public void setFeatureModel(IFeatureModel featureModel) {
		reader.featureModel = featureModel;
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return reader.featureModel;
	}

	/**
	 * Reads a feature model from a string.
	 *
	 * Please use {@link #setFile(IFile)} if you know the source of the feature model.
	 *
	 * @param text the textual representation of the feature model
	 * @throws UnsupportedModelException
	 */
	@Override
	public void readFromString(String text) throws UnsupportedModelException {
		reader.readFromString(text);
	}

	public void readFromFile(IFile ifile) throws UnsupportedModelException, FileNotFoundException {
		////
		FMComposerManager.getFMComposerExtension(ifile.getProject());
		/////
		final File file = ifile.getRawLocation().makeAbsolute().toFile();

		reader.readFromFile(file);
	}

	@Override
	public void readFromFile(File file) throws FileNotFoundException, UnsupportedModelException {
		reader.readFromFile(file);
	}

	@Override
	public List<Problem> getWarnings() {
		return reader.getWarnings();
	}

	public AbstractFeatureModelReader getReader() {
		return reader;
	}

	@Override
	protected void parseInputStream(InputStream inputStream) throws UnsupportedModelException {
		reader.parseInputStream(inputStream);
	}

	/**
	 * Set the source file of the textual representation of the feature model.
	 *
	 * @see #setFile(File)
	 * @param featureModelFile
	 */
	public void setFile(IFile featureModelFile) {
		reader.setFile(featureModelFile.getRawLocation().makeAbsolute().toFile());
	}
}
