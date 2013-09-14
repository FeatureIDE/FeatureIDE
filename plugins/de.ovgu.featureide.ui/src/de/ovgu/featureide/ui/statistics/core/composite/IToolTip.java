package de.ovgu.featureide.ui.statistics.core.composite;

import de.ovgu.featureide.ui.statistics.ui.helper.TreeLabelProvider;

/**
 * Interface to explicitly make nodes have tool tips. 
 * 
 * @see TreeLabelProvider
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public interface IToolTip {
	/**
	 * @return tool-tip text to be displayed.
	 */
	public String getToolTip();
}