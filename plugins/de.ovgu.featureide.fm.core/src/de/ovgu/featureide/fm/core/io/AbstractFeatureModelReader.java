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

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * Default reader to be extended for each feature model format.
 *
 * If IFile support is needed, the {@link FeatureModelReaderIFileWrapper} has to be used.
 *
 * @deprecated Use {@link IFeatureModelFormat} and {@link FileHandler} instead.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
@Deprecated
public abstract class AbstractFeatureModelReader implements IFeatureModelReader {

	/**
	 * the structure to store the parsed data
	 */
	protected IFeatureModel featureModel;

	/**
	 * warnings occurred while parsing
	 */
	protected LinkedList<Problem> warnings = new LinkedList<Problem>();

	/**
	 * The source of the textual representation of the feature model.<br/><br/>
	 *
	 * <strong>Caution:</strong> This field can be null and is maybe not up to date.
	 */
	protected File featureModelFile;

	@Override
	public void setFeatureModel(IFeatureModel featureModel) {
		this.featureModel = featureModel;
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	/**
	 * Reads a feature model from a file.
	 *
	 * @param file the file which contains the textual representation of the feature model
	 * @throws UnsupportedModelException
	 * @throws FileNotFoundException
	 */
	@Override
	public void readFromFile(File file) throws UnsupportedModelException, FileNotFoundException {
		warnings.clear();
		featureModelFile = file;
		final String fileName = file.getPath();
		InputStream inputStream = null;
		try {
			inputStream = new FileInputStream(fileName);
			parseInputStream(inputStream);
			// TODO: REMOVE THIS, THIS IS A HACK
			// THIS IS A HACK
			featureModel.setSourceFile(file.toPath());
			// END HACK
		} finally {
			if (inputStream != null) {
				try {
					inputStream.close();
				} catch (final IOException e) {
					Logger.logError(e);
				}
			}
		}
	}

	/**
	 * Reads a feature model from a string.<br/><br/>
	 *
	 * Please use {@link #setFile(File)} if you know the source of the feature model.
	 *
	 * @param text the textual representation of the feature model
	 * @throws UnsupportedModelException
	 */
	@Override
	public void readFromString(String text) throws UnsupportedModelException {
		warnings.clear();
		final InputStream inputStream = new ByteArrayInputStream(text.getBytes(Charset.availableCharsets().get("UTF-8")));
		parseInputStream(inputStream);
	}

	@Override
	public List<Problem> getWarnings() {
		return warnings;
	}

	/**
	 * Reads a feature model from an input stream.
	 *
	 * @param inputStream the textual representation of the feature model
	 * @throws UnsupportedModelException
	 */
	protected abstract void parseInputStream(InputStream inputStream) throws UnsupportedModelException;

	/**
	 * Set the source file of the textual representation of the feature model.
	 *
	 * @param featureModelFile the source file
	 */
	@Override
	public void setFile(File featureModelFile) {
		this.featureModelFile = featureModelFile;
	}

	public File getFile() {
		return featureModelFile;
	}
}
