package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;

/**
 * Parent node which evaluates if it has children before actually displaying
 * them. All features are sorted in an alphabetical order ignoring the case.
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public final class FeatureListNode extends LazyParent {
	private Collection<Feature> list;
	
	public FeatureListNode(String description, Collection<Feature> collection) {
		this(description, collection, collection.size());
	}

	public FeatureListNode(String description, Collection<Feature> collection, Object value) {
		super(description, value);
		
		List<Feature> list = new LinkedList<Feature>(collection);
		Collections.sort(list, new Comparator<Feature>() {
			@Override
			public int compare(Feature o1, Feature o2) {
				return o1.getName().compareToIgnoreCase(o2.getName());
			}
		});
		
		this.list = list;
		lazy = (list.size() != 0);
	}
	
	@Override
	protected void initChildren() {
		for (Feature feat : list) {
			addChild(new FeatureNode(feat));
		}
	}
}