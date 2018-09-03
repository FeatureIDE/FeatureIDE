package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import org.abego.treelayout.NodeExtentProvider;

import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;

/**
 * Provides the extent (width and height) of the graphical representation of a Feature to abego library
 *
 * @author Lukas Vogt
 * @author Martha Nyerembe
 */

public class GFNodeExtentProvider implements NodeExtentProvider<IGraphicalFeature> {

	@Override
	public double getHeight(IGraphicalFeature feature) {
		return feature.getSize().height();
	}

	@Override
	public double getWidth(IGraphicalFeature feature) {
		return feature.getSize().width();
	}

}
