/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.io;

import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.velvet.VelvetFeatureModelReader;
import de.ovgu.featureide.fm.core.io.velvet.VelvetFeatureModelWriter;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;

/**
 * 
 * @author Sebastian Krieter
 */
public abstract class ModelIOFactory {
	
	public static final int
		TYPE_UNKNOWN = -1,
		TYPE_XML = 0,
		TYPE_VELVET = 1;
	
	public static AbstractFeatureModelReader getModelReader(int type) {
		return getModelReader(getNewFeatureModel(type), type);
	}
	
	public static AbstractFeatureModelWriter getModelWriter(int type) {
		return getModelWriter(getNewFeatureModel(type), type);
	}
	
	public static AbstractFeatureModelReader getModelReader(FeatureModel featureModel, int type) {
		switch (type) {
		case TYPE_XML:
			return new XmlFeatureModelReader(featureModel);
		case TYPE_VELVET:
			return new VelvetFeatureModelReader(featureModel);
		default:
			return null;
		}
	}
	
	public static AbstractFeatureModelWriter getModelWriter(FeatureModel featureModel, int type) {
		switch (type) {
		case TYPE_XML:
			return new XmlFeatureModelWriter(featureModel);
		case TYPE_VELVET:
			return new VelvetFeatureModelWriter(featureModel);
		default:
			return null;
		}
	}
	
	public static int getTypeByFileName(String fileName) {
		if (fileName.endsWith(".xml")) {
			return TYPE_XML;
		} else if (fileName.endsWith(".velvet")) {
			return TYPE_VELVET;
		}
		return TYPE_UNKNOWN;
	}
	
	public static FeatureModel getNewFeatureModel(int type) {
		switch (type) {
		case TYPE_XML:
			return new FeatureModel();
		case TYPE_VELVET:
			return new ExtendedFeatureModel();
		default:
			return null;
		}
	}
			
}
