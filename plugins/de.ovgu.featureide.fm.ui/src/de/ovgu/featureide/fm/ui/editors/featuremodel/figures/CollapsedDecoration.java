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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;


import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.draw2d.Shape;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * A decoration for a feature connection that indicates the mandatory property.
 * 
 * @author Joshua Sprey
 * @author Enis Belli
 * @author Christopher Sontag
 * @author Maximilian Kühl
 */
public class CollapsedDecoration extends Shape implements RotatableDecoration, GUIDefaults {
	private static int counter = 0;
	private final Label childrenCount = new Label();
	//	private static GridLayout gl = new GridLayout();
	private static final FreeformLayout layout = new FreeformLayout();

	private IGraphicalFeature graphicalFeature;

	public CollapsedDecoration(IGraphicalFeature parent) {
		super();
		graphicalFeature = parent;
		setLayoutManager(layout);
		setBackgroundColor(FMPropertyManager.getConcreteFeatureBackgroundColor());
		setBorder(FMPropertyManager.getFeatureBorder(false));

		childrenCount.setFont(DEFAULT_FONT);
		setDecoratorText("" + parent.getObject().getStructure().getChildrenCount());
		
		FMUIPlugin.getDefault().logInfo("" + parent.getObject().getName() + "|" + (counter++));
		add(childrenCount);
	}

	@Override
	public void setLocation(Point p) {
//		super.setLocation(p.translate(-(getBounds().width / 2), GUIDefaults.COLLAPSED_DECORATOR_FEATURE_SPACE));
		super.setLocation(p);
	}

	public void setDecoratorText(String newText) {
		if (childrenCount.getText().equals(newText)) {
			return;
		}
		childrenCount.setText(newText);

		final Dimension labelSize = childrenCount.getPreferredSize();
		this.minSize = labelSize;

		if (!labelSize.equals(childrenCount.getSize())) {
			childrenCount.setBounds(
					new Rectangle(GUIDefaults.COLLAPSED_DECORATOR_X_SPACE, GUIDefaults.COLLAPSED_DECORATOR_Y_SPACE, labelSize.width, labelSize.height));

			final Rectangle bounds = getBounds();
			labelSize.width += GUIDefaults.COLLAPSED_DECORATOR_X_SPACE * 2;
			labelSize.height += GUIDefaults.COLLAPSED_DECORATOR_Y_SPACE * 2;
			bounds.setSize(labelSize);

			final Dimension oldSize = getSize();
			if (!oldSize.equals(0, 0)) {
				bounds.x += (oldSize.width - bounds.width) >> 1;
			}
			setBounds(bounds);
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.draw2d.RotatableDecoration#setReferencePoint(org.eclipse.draw2d.geometry.Point)
	 */
	@Override
	public void setReferencePoint(Point p) {

	}

	/* (non-Javadoc)
	 * @see org.eclipse.draw2d.Shape#fillShape(org.eclipse.draw2d.Graphics)
	 */
	@Override
	protected void fillShape(Graphics graphics) {
	}

	/* (non-Javadoc)
	 * @see org.eclipse.draw2d.Shape#outlineShape(org.eclipse.draw2d.Graphics)
	 */
	@Override
	protected void outlineShape(Graphics graphics) {

	}

}
