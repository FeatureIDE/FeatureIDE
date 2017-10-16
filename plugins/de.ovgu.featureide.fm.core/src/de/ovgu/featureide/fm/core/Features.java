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
package de.ovgu.featureide.fm.core;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Convenience methods for traversing the feature tree structure.
 *
 * @author Sebastian Krieter
 */
public final class Features {

	public static final String FEATURE_SUFFIX = "(Feature)";

	public static Collection<IFeatureStructure> getAllFeatures(final Collection<IFeatureStructure> features, final IFeatureStructure root) {
		return getAllFeatures(features, root, true);
	}

	public static Collection<IFeatureStructure> getLeafFeatures(final Collection<IFeatureStructure> features, final IFeatureStructure root) {
		return getLeafFeatures(features, root, true);
	}

	public static Collection<IFeatureStructure> getCompoundFeatures(final Collection<IFeatureStructure> features, final IFeatureStructure root) {
		return getCompoundFeatures(features, root, true);
	}

	public static Collection<IFeatureStructure> getAllFeatures(final Collection<IFeatureStructure> features, final IFeatureStructure root,
			boolean includeRoot) {
		if (includeRoot) {
			features.add(root);
		}
		for (final IFeatureStructure feature : root.getChildren()) {
			getAllFeatures(features, feature, true);
		}
		return features;
	}

	public static Collection<IFeatureStructure> getLeafFeatures(final Collection<IFeatureStructure> features, final IFeatureStructure root,
			boolean includeRoot) {
		if (includeRoot && !root.hasChildren()) {
			features.add(root);
		}
		for (final IFeatureStructure feature : root.getChildren()) {
			getLeafFeatures(features, feature, true);
		}
		return features;
	}

	public static Collection<IFeatureStructure> getCompoundFeatures(final Collection<IFeatureStructure> features, final IFeatureStructure root,
			boolean includeRoot) {
		if (includeRoot && root.hasChildren()) {
			features.add(root);
		}
		for (final IFeatureStructure feature : root.getChildren()) {
			getCompoundFeatures(features, feature, true);
		}
		return features;
	}

	public static final Collection<String> extractOperatorNamesFromFeatuers(final Set<String> features) {
		final List<String> result = new ArrayList<>();
		for (final String feature : features) {
			final String str = feature.toLowerCase().trim();
			if (Operator.isOperatorName(str)) {
				result.add(str);
			}
		}
		return result;
	}

	public static IFeature getCommonAncestor(Collection<IFeature> features) {
		List<IFeature> commonAncestorList = null;
		for (final IFeature feature : features) {
			commonAncestorList = Features.getCommonAncestor(commonAncestorList, FeatureUtils.getParent(feature));
		}
		return commonAncestorList.get(commonAncestorList.size() - 1);
	}

	public static List<IFeature> getCommonAncestor(List<IFeature> commonAncestorList, IFeature parent) {
		if (commonAncestorList == null) {
			commonAncestorList = new LinkedList<>();
			while (parent != null) {
				commonAncestorList.add(0, parent);
				parent = FeatureUtils.getParent(parent);
			}
		} else if (parent != null) {
			final LinkedList<IFeature> parentList = new LinkedList<>();
			while (parent != null) {
				parentList.addFirst(parent);
				parent = FeatureUtils.getParent(parent);
			}
			final Iterator<IFeature> iterator1 = parentList.iterator();
			final Iterator<IFeature> iterator2 = commonAncestorList.iterator();
			int i = 0;
			while (iterator1.hasNext() && iterator2.hasNext()) {
				if (!iterator1.next().equals(iterator2.next())) {
					break;
				}
				i++;
			}
			commonAncestorList = commonAncestorList.subList(0, i);
		}
		return commonAncestorList;
	}

}
