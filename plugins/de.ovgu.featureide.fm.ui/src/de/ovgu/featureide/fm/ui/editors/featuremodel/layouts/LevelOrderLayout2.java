/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.layouts;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * Layouts the features at the feature diagram using a reverse level order
 * search.
 * 
 * @author Christopher Sontag
 */
public class LevelOrderLayout2 extends FeatureDiagramLayoutManager {

	public LevelOrderLayout2() {
		super();
	}
	
	@Override
	protected void layoutFeatureModel(IGraphicalFeatureModel featureModel) {
		IGraphicalFeature root = FeatureUIHelper.getGraphicalRootFeature(featureModel);
		layout(root);
	}
	
	public void layout(IGraphicalFeature root) {
		LinkedList<LinkedList<IGraphicalFeature>> levels = calculateLevels(root);
		Iterator<LinkedList<IGraphicalFeature>> iterator = levels.descendingIterator();
		
		int curLevel = levels.size() - 1;
		while (iterator.hasNext()) {
			LinkedList<IGraphicalFeature> level = iterator.next();
			layoutLevel(level, curLevel--);
		}
	}

	/**
	 * Calculates the levels containing all features of a level in a linked list
	 * @param root The root feature
	 * @return The level representation of the feature model
	 */
	private LinkedList<LinkedList<IGraphicalFeature>> calculateLevels(IGraphicalFeature root) {
		LinkedList<LinkedList<IGraphicalFeature>> levels = new LinkedList<LinkedList<IGraphicalFeature>>();

		LinkedList<IGraphicalFeature> level = new LinkedList<IGraphicalFeature>();
		level.add(root);

		while (!level.isEmpty()) {
			levels.add(level);
			LinkedList<IGraphicalFeature> newLevel = new LinkedList<IGraphicalFeature>();
			for (IGraphicalFeature feature : level) {
				for (IGraphicalFeature child : getChildren(feature)) {
					if (!child.getObject().getStructure().hasHiddenParent() || !child.getObject().getStructure().hasCollapsedParent())
						newLevel.add(child);
				}
			}
			level = newLevel;
		}

		return levels;
	}
	
	private void layoutLevel(LinkedList<IGraphicalFeature> levelItems, int curLevel) {
		for (IGraphicalFeature feature : levelItems) {
			if (feature.getObject().getStructure().hasChildren()) {
				centerAboveChildren(feature);
			}
			feature.setLocation(feature.getLocation().setY(50 * curLevel));
		}
		
//		
//		IGraphicalFeature leftSibling = null;
//		int width = FMPropertyManager.getLayoutMarginX();
//		for (IGraphicalFeature item : levelItems) {
//			Point location = new Point();
//			location.setY(FMPropertyManager.getLayoutMarginY() + FMPropertyManager.getFeatureSpaceY() * curLevel);
//			if (leftSibling != null) {
//				if (item.getObject().getStructure().getParent() != leftSibling.getObject().getStructure().getParent()) {
//					width += 2 * FMPropertyManager.getFeatureSpaceX() + item.getSize().width;
//				} else {
//					width += FMPropertyManager.getFeatureSpaceX() + item.getSize().width;
//				}
//				location.setX(width);
//			}
//			item.setLocation(location);
//			leftSibling = item;
//		}
	}
	
	private void centerAboveChildren(IGraphicalFeature feature) {
		final List<IGraphicalFeature> graphicalChildren = getChildren(feature);
		int minX = getBounds(graphicalChildren.get(0)).x;
		int maxX = getBounds(graphicalChildren.get(graphicalChildren.size() - 1)).right();
		Point location = getLocation(feature);
		int x = (maxX + minX) / 2 - feature.getSize().width / 2;
		feature.setLocation(new Point(x, location.y));
	}
	
}
