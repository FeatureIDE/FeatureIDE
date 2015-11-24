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
package de.ovgu.featureide.fm.core.base.impl;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelReader;
import de.ovgu.featureide.fm.core.io.ModelIOFactory;
import de.ovgu.featureide.fm.core.io.ModelWarning;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * 
 * @author Sebastian Krieter
 */
public class DefaultFeatureModelFactory implements IFeatureModelFactory {

	public static final String ID = FMCorePlugin.PLUGIN_ID + ".DefaultFeatureModelFactory";

	public static DefaultFeatureModelFactory getInstance() {
		return new DefaultFeatureModelFactory();
	}

	private DefaultFeatureModelFactory() {
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public Constraint createConstraint(IFeatureModel featureModel, Node propNode) {
		return new Constraint(featureModel, propNode);
	}

	@Override
	public Feature createFeature(IFeatureModel featureModel, String name) {
		return new Feature(featureModel, name);
	}

	@Override
	public FeatureModel createFeatureModel() {
		return new FeatureModel();
	}

	@Override
	public List<ModelWarning> loadFeatureModel(IFeatureModel featureModel, File file) {
		featureModel.setSourceFile(file);
		AbstractFeatureModelReader reader = ModelIOFactory.getModelReader(featureModel, ModelIOFactory.getTypeByFileName(file.getName()));
		try {
			reader.readFromFile(file);
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (UnsupportedModelException e) {
			List<ModelWarning> w = new ArrayList<>();
			w.add(new ModelWarning(e.getMessage(), e.lineNumber, IMarker.SEVERITY_ERROR));
			return w;
		}
		return reader.getWarnings();
	}
	
	@Override
	public List<ModelWarning> loadFeatureModel(IFeatureModel featureModel, String content) {
		AbstractFeatureModelReader reader = ModelIOFactory.getModelReader(featureModel, ModelIOFactory.TYPE_XML);
		try {
			reader.readFromString(content);
		} catch (UnsupportedModelException e) {
			List<ModelWarning> w = new ArrayList<>();
			w.add(new ModelWarning(e.getMessage(), e.lineNumber, IMarker.SEVERITY_ERROR));
			return w;
		}
		return reader.getWarnings();
	}

}
