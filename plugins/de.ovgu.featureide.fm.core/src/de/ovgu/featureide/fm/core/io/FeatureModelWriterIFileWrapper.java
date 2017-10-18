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
import java.io.InputStream;
import java.nio.charset.Charset;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * This Wrapper makes it possible, to write feature models to IFiles, e.g. if working with Eclipse plugins Otherwise only the classes extending
 * {@link AbstractFeatureModelWriter} are needed
 *
 * @deprecated Use {@link IFeatureModelFormat} and {@link FileHandler} instead. <br/> {@link IFile} can be converted via
 *             {@code Paths.getPath(ifile.getLocationURI())}.
 *
 * @author S�nke Holthusen
 * @author Marcus Pinnecke (Feature Interface)
 */
@Deprecated
public class FeatureModelWriterIFileWrapper extends AbstractFeatureModelWriter {

	private final IFeatureModelWriter writer;

	public FeatureModelWriterIFileWrapper(IFeatureModelWriter writer) {
		this.writer = writer;
	}

	@Override
	public void setFeatureModel(IFeatureModel featureModel) {
		writer.setFeatureModel(featureModel);
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return writer.getFeatureModel();
	}

	@Override
	public void writeToFile(File file) {
		writer.writeToFile(file);
	}

	@Override
	public String writeToString() {
		return writer.writeToString();
	}

	public void writeToFile(IFile file) throws CoreException {
		final InputStream source = new ByteArrayInputStream(writeToString().getBytes(Charset.availableCharsets().get("UTF-8")));
		if (file.exists()) {
			file.setContents(source, false, true, null);
		} else {
			file.create(source, false, null);
		}
	}
}
