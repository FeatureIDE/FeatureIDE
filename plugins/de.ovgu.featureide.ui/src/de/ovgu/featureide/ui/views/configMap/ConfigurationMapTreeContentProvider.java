/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistributefeatureRoots/or modify
 * it under the terms of the GNU LfeatureRootseneral PufeatureRootscense as published by
 * the FrefeatureRootsare Foundation, either version 3 of the License, or
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
package de.ovgu.featureide.ui.views.configMap;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.AbstractTreeViewer;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.io.ConfigurationLoader;

/**
 * TODO description
 * 
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 */
public class ConfigurationMapTreeContentProvider implements ITreeContentProvider {
	private ConfigurationLoader loader;
	private List<Configuration> configurations;

	private IFeatureProject featureProject;
	private Object[] featureRoots;

	public ConfigurationMapTreeContentProvider() {
		loader = new ConfigurationLoader();
	}

	/**
	 * @param featureProject
	 */
	public void setFeatureProject(IFeatureProject featureProject) {
		if (this.featureProject != featureProject) {
			this.featureProject = featureProject;
			configurations = loader.loadConfigurations(featureProject.getFeatureModel(), featureProject.getConfigPath());
			List<IFeature> featureRootList = new ArrayList<>();
			for (IFeature feature : featureProject.getFeatureModel().getFeatures()) {
				if (feature.getStructure().getParent() == null)
					featureRootList.add(feature);
			}
			featureRoots = featureRootList.toArray();
		}
	}

	/**
	 * {@inheritDoc}
	 * <p>
	 * <b>NOTE:</b> The returned array must not contain the given
	 * <code>inputElement</code>, since this leads to recursion issues in
	 * {@link AbstractTreeViewer} (see
	 * <a href="https://bugs.eclipse.org/9262">bug 9262</a>).
	 * </p>
	 */
	@Override
	public Object[] getElements(Object inputElement) {
		return featureRoots;
	}

	/**
	 * Returns the child elements of the given parent element.
	 * <p>
	 * The difference between this method and <code>IStructuredContentProvider.getElements</code>
	 * is that <code>getElements</code> is called to obtain the
	 * tree viewer's root elements, whereas <code>getChildren</code> is used
	 * to obtain the children of a given parent element in the tree (including a root).
	 * </p>
	 * The result is not modified by the viewer.
	 *
	 * @param parentElement the parent element
	 * @return an array of child elements
	 */
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IFeature) {
			IFeature f = (IFeature) parentElement;
			List<IFeatureStructure> childStructures = f.getStructure().getChildren();
			Object[] children = new Object[childStructures.size()];
			int i = 0;
			for (IFeatureStructure struct : childStructures)
				children[i++] = struct.getFeature();
			return children;
		}
		return null;
	}

	/**
	 * Returns the parent for the given element, or <code>null</code>
	 * indicating that the parent can't be computed.
	 * In this case the tree-structured viewer can't expand
	 * a given node correctly if requested.
	 *
	 * @param element the element
	 * @return the parent element, or <code>null</code> if it
	 *         has none or if the parent cannot be computed
	 */
	public Object getParent(Object element) {
		if (element instanceof IFeature) {
			IFeature f = (IFeature) element;
			return f.getStructure().getParent().getFeature();
		}
		return null;
	}

	/**
	 * Returns whether the given element has children.
	 * <p>
	 * Intended as an optimization for when the viewer does not
	 * need the actual children. Clients may be able to implement
	 * this more efficiently than <code>getChildren</code>.
	 * </p>
	 *
	 * @param element the element
	 * @return <code>true</code> if the given element has children,
	 *         and <code>false</code> if it has no children
	 */
	public boolean hasChildren(Object element) {
		if (element instanceof IFeature) {
			IFeature f = (IFeature) element;
			return f.getStructure().hasChildren();
		}
		return false;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IContentProvider#inputChanged(org.eclipse.jface.viewers.Viewer, java.lang.Object, java.lang.Object)
	 */
	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IContentProvider#dispose()
	 */
	@Override
	public void dispose() {}
}
