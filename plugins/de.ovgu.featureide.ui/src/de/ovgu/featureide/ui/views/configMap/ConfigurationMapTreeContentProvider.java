/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistributefiltersRoots/or modify
 * it under the terms of the filtersatureRootfilters PufeatureRootscense as publishefilters the FrefeatureRootsare Foundation, either version 3 of the License, or
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
import java.util.Collections;
import java.util.List;

import org.eclipse.jface.viewers.AbstractTreeViewer;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * ContentProvider for the tree ConfigurationMap
 *
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 */
public class ConfigurationMapTreeContentProvider implements ITreeContentProvider, IConfigurationMapFilterable {

	private static final Object[] emptyRoot = new Object[] { StringTable.PLEASE_OPEN_A_FEATURE_DIAGRAM_EDITOR };

	private IFeatureProject featureProject;
	private Object[] featureRoots = emptyRoot;

	private final ConfigurationMap configurationMap;

	public ConfigurationMapTreeContentProvider(ConfigurationMap configurationMap) {
		this.configurationMap = configurationMap;
	}

	@Override
	public boolean addFilter(IConfigurationMapFilter filter) {
		if (featureProject != null) {
			if (!hasFilter(filter) && configurationMap.getFilters().add(filter)) {
				filter.initialize(configurationMap);
				updateElements();
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean removeFilter(IConfigurationMapFilter filter) {
		if (featureProject != null) {
			if (hasFilter(filter) && configurationMap.getFilters().remove(filter)) {
				updateElements();
				return true;
			}
		}

		return false;
	}

	@Override
	public boolean hasFilter(IConfigurationMapFilter filter) {
		return configurationMap.getFilters().contains(filter);
	}

	public void setFeatureProject(IFeatureProject featureProject) {
		if (this.featureProject != featureProject) {
			this.featureProject = featureProject;
			if (featureProject != null) {
				for (final IConfigurationMapFilter filter : configurationMap.getFilters()) {
					filter.initialize(configurationMap);
				}
			}
			updateElements();
		}
	}

	public void updateElements() {
		if (featureProject == null) {
			featureRoots = emptyRoot;
			return;
		}

		final List<Object> featureRootList = new ArrayList<>();

		// add Features
		for (final IFeature feature : featureProject.getFeatureModel().getFeatures()) {
			// getParent(feature) == null <=> With the used filter, this feature is a root (although originally it may be not).
			if (filter(feature) && !hasVisibleParent(feature)) {
				featureRootList.add(feature);
			}
		}

		Collections.reverse(featureRootList);
		featureRoots = featureRootList.toArray();

		configurationMap.updateTree();
	}

	/**
	 * {@inheritDoc} <p> <b>NOTE:</b> The returned array must not contain the given <code>inputElement</code>, since this leads to recursion issues in
	 * {@link AbstractTreeViewer} (see <a href="https://bugs.eclipse.org/9262">bug 9262</a>). </p>
	 */
	@Override
	public Object[] getElements(Object inputElement) {
		return featureRoots;
	}

	private boolean hasVisibleParent(IFeature feature) {
		if (feature.getStructure().getParent() != null) {
			return filter(feature.getStructure().getParent().getFeature());
		}
		return false;
	}

	/**
	 * Returns the child elements of the given parent element. <p> The difference between this method and <code>IStructuredContentProvider.getElements</code> is
	 * that <code>getElements</code> is called to obtain the tree viewer's root elements, whereas <code>getChildren</code> is used to obtain the children of a
	 * given parent element in the tree (including a root). </p> The result is not modified by the viewer.
	 *
	 * @param parentElement the parent element
	 * @return an array of child elements
	 */
	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IFeature) {
			final IFeature f = (IFeature) parentElement;
			final List<IFeatureStructure> childStructures = f.getStructure().getChildren();

			final List<Object> children = new ArrayList<>();
			for (final IFeatureStructure struct : childStructures) {
				final IFeature child = struct.getFeature();
				if (filter(child)) {
					children.add(child);
				}
			}

			return children.toArray();
		}

		return null;
	}

	/**
	 * Returns the parent for the given element, or <code>null</code> indicating that the parent can't be computed. In this case the tree-structured viewer
	 * can't expand a given node correctly if requested.
	 *
	 * @param element the element
	 * @return the parent element, or <code>null</code> if it has none or if the parent cannot be computed
	 */
	@Override
	public Object getParent(Object element) {
		if (element instanceof IFeature) {
			final IFeature feature = (IFeature) element;
			final IFeatureStructure parentStructure = feature.getStructure().getParent();
			if (parentStructure != null) {
				return filter(parentStructure.getFeature());
			}
		}
		return null;
	}

	/**
	 * Returns whether the given element has children. <p> Intended as an optimization for when the viewer does not need the actual children. Clients may be
	 * able to implement this more efficiently than <code>getChildren</code>. </p>
	 *
	 * @param element the element
	 * @return <code>true</code> if the given element has children, and <code>false</code> if it has no children
	 */
	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof IFeature) {
			final IFeature f = (IFeature) element;

			for (final IFeatureStructure childStruct : f.getStructure().getChildren()) {
				// If at least one child is valid, the feature has children.
				return filter(childStruct.getFeature());
			}
		}

		return false;
	}

	private boolean filter(IFeature feature) {
		// OR
		for (final IConfigurationMapFilter filter : configurationMap.getFilters()) {
			if (filter.test(configurationMap, feature)) {
				return true;
			}
		}

		return false;
	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

	@Override
	public void dispose() {}

}
