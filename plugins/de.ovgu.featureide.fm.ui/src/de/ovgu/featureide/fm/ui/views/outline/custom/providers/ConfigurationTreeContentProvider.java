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
package de.ovgu.featureide.fm.ui.views.outline.custom.providers;

import java.nio.file.Paths;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.ui.views.outline.computations.ComputationHeader;
import de.ovgu.featureide.fm.ui.views.outline.computations.ConfigurationComputationBundle;
import de.ovgu.featureide.fm.ui.views.outline.computations.IConfigurationComputation;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider;

/**
 * TODO description
 *
 * @author Chico Sundermann
 */
public class ConfigurationTreeContentProvider extends OutlineTreeContentProvider {

	private IFeatureModel fModel;
	private Configuration config;

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		if (newInput != null) {
			if (newInput instanceof Configuration) {
				config = ((Configuration) newInput);
				fModel = config.getFeatureModel();
			} else if (newInput instanceof IFile) {
				if (((IFile) newInput).exists()) {
					try {
						final ConfigurationManager confManager = ConfigurationManager.getInstance(Paths.get(((IFile) newInput).getLocationURI()));
						config = confManager.getObject();
						fModel = config.getFeatureModel();
					} catch (final ClassCastException e) {}
				}
			}
		}
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider#getElements(java.lang.Object)
	 */
	@Override
	public Object[] getElements(Object inputElement) {
		final ConfigurationComputationBundle computationBundle = new ConfigurationComputationBundle();
		computationBundle.initComputations(config);
		return computationBundle.getComputationHeaders().toArray();
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider#getChildren(java.lang.Object)
	 */
	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof ComputationHeader) {
			final IConfigurationComputation[] computations = new IConfigurationComputation[1];
			computations[0] = ((ComputationHeader) parentElement).getComputation();
			return computations;
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider#getParent(java.lang.Object)
	 */
	@Override
	public Object getParent(Object element) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider#hasChildren(java.lang.Object)
	 */
	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof ComputationHeader) {
			return true;
		}
		return false;
	}

}
