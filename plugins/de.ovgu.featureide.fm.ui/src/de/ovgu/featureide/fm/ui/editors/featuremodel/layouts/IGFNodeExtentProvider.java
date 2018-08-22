package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import org.abego.treelayout.NodeExtentProvider;

import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;

public class IGFNodeExtentProvider implements NodeExtentProvider<IGraphicalFeature> {

	/*
	 * (non-Javadoc)
	 * @see org.abego.treelayout.NodeExtentProvider#getHeight(java.lang.Object)
	 */
	@Override
	public double getHeight(IGraphicalFeature arg0) {
		// TODO Auto-generated method stub
		return arg0.getSize().height();
	}

	/*
	 * (non-Javadoc)
	 * @see org.abego.treelayout.NodeExtentProvider#getWidth(java.lang.Object)
	 */
	@Override
	public double getWidth(IGraphicalFeature arg0) {
		// TODO Auto-generated method stub
		return arg0.getSize().width();
	}

}
