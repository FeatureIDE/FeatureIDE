/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.fm.core.io;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;

import featureide.fm.core.FeatureModel;

/**
 * Default reader to be extended for each feature model format.
 * 
 * @author Thomas Thuem
 */
public abstract class AbstractFeatureModelReader implements IFeatureModelReader {

	/**
	 * the structure to store the parsed data
	 */
	protected FeatureModel featureModel;
	
	/**
	 * warnings occurred while parsing
	 */
	protected LinkedList<ModelWarning> warnings = new LinkedList<ModelWarning>();
	
	public void setFeatureModel(FeatureModel featureModel) {
		this.featureModel = featureModel;
	}
	
	public FeatureModel getFeatureModel() {
		return featureModel;
	}
	
	public void readFromFile(IFile file) throws UnsupportedModelException, FileNotFoundException {
		warnings.clear();
		String fileName = file.getRawLocation().toOSString();		
        InputStream inputStream = new FileInputStream(fileName);
        parseInputStream(inputStream);
 	}
	
	@Override
	public void readFromFile(File file) throws UnsupportedModelException, FileNotFoundException {
		warnings.clear();
		String fileName = file.getPath();		
        InputStream inputStream = new FileInputStream(fileName);
        parseInputStream(inputStream);
 	}

	public void readFromString(String text) throws UnsupportedModelException {
		warnings.clear();
        InputStream inputStream = new ByteArrayInputStream(text.getBytes());
        parseInputStream(inputStream);
 	}
	
	public List<ModelWarning> getWarnings() {
		return warnings;
	}

	/**
	 * Reads a feature model from an input stream.
	 * 
	 * @param  inputStream  the textual representation of the feature model
	 * @throws UnsupportedModelException
	 */
	protected abstract void parseInputStream(InputStream inputStream)
			throws UnsupportedModelException;
	
}
