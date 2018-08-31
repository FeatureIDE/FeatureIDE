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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureModelLayout;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * A decoration for a feature connection that indicates the mandatory property.
 *
 * @author Joshua Sprey
 * @author Enis Belli
 * @author Christopher Sontag
 * @author Maximilian Kühl
 * @author Martha Nyerembe
 * @author Lukas Vogt
 */
public class CollapsedDecoration extends ConnectionDecoration implements GUIDefaults {

	private final Label childrenCount = new Label();
	// private static GridLayout gl = new GridLayout();
	private static final FreeformLayout layout = new FreeformLayout();

	private IGraphicalFeature graphicalFeature;

	public boolean isLegendEntry = false;

	public CollapsedDecoration(IGraphicalFeature parent) {
		super();
		graphicalFeature = parent;
		setLayoutManager(layout);
		setBackgroundColor(FMPropertyManager.getDiagramBackgroundColor());
		setForegroundColor(FMPropertyManager.getFeatureForgroundColor());

		childrenCount.setFont(DEFAULT_FONT);
		setOpaque(true);
		setDecoratorText("" + GetAllChildren(parent.getObject().getStructure()));
		add(childrenCount);
	}

	/***
	 * COnstructor for the collapsed decoration figure of the legend
	 */
	public CollapsedDecoration() {
		super();
		setLayoutManager(layout);
		setBackgroundColor(FMPropertyManager.getDiagramBackgroundColor());
		setForegroundColor(FMPropertyManager.getFeatureForgroundColor());

		isLegendEntry = true;

		setOpaque(true);
		childrenCount.setFont(DEFAULT_FONT);
		setDecoratorText("");
		childrenCount.setText("");
		add(childrenCount);
	}

	@Override
	public void setLocation(Point p) {
		if (isLegendEntry) {
			super.setLocation(p);
			return;
		}

		if (graphicalFeature != null) {
			final FeatureModelLayout layout = graphicalFeature.getGraphicalModel().getLayout();
			// set Collapse position for abego treeLayout
			if (layout.isUsesAbegoTreeLayout()) {
				switch (layout.getAbegoRootposition()) {
				case Left:
					super.setLocation(p.translate((+getBounds().width / 2) + 4, (getBounds().height / 2) - 9));
				case Right:
					super.setLocation(p.translate((-getBounds().width / 2) + 1, getBounds().height / 2));
				case Bottom:
					super.setLocation(p.translate((+getBounds().width / 2) + GUIDefaults.COLLAPSED_DECORATOR_FEATURE_SPACE, -getBounds().height + 3));
				default:
					super.setLocation(p.translate(-(getBounds().width / 2) + 1, GUIDefaults.COLLAPSED_DECORATOR_FEATURE_SPACE));
				}
			}

			if (graphicalFeature.getGraphicalModel().getLayout().getLayoutAlgorithm() == 4) {
				// left to right layout
				super.setLocation(p.translate((+getBounds().width / 2) + GUIDefaults.COLLAPSED_DECORATOR_FEATURE_SPACE, -getBounds().height / 2));
			}
		}
		super.setLocation(p.translate(-(getBounds().width / 2), GUIDefaults.COLLAPSED_DECORATOR_FEATURE_SPACE));
	}

	public int GetAllChildren(IFeatureStructure parent) {
		int count = 0;
		for (final IFeatureStructure iterable_element : parent.getChildren()) {
			count += 1 + GetAllChildren(iterable_element);
		}
		return count;
	}

	public void setDecoratorText(String newText) {
		if (childrenCount.getText().equals(newText)) {
			return;
		}
		childrenCount.setText(newText);

		final Dimension labelSize = childrenCount.getPreferredSize();
		minSize = labelSize;

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

	@Override
	public void setReferencePoint(Point p) {

	}

	@Override
	protected void fillShape(Graphics graphics) {}

	@Override
	protected void outlineShape(Graphics graphics) {
		if (isLegendEntry) {
			graphics.setLineWidth(1);
			graphics.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
			graphics.fillRoundRectangle(getBounds(), GUIDefaults.COLLAPSED_DECORATOR_ARC_RADIUS, GUIDefaults.COLLAPSED_DECORATOR_ARC_RADIUS);
			graphics.drawRoundRectangle(getBounds(), GUIDefaults.COLLAPSED_DECORATOR_ARC_RADIUS, GUIDefaults.COLLAPSED_DECORATOR_ARC_RADIUS);
			return;
		}
		final int x = getBounds().x + 1;
		final int y = getBounds().y + 1;
		int width = getBounds().width - 2;
		if ((width % 2) == 1) {
			width += 1;
			setBounds(new Rectangle(getBounds().x, getBounds().y, getBounds().width + 1, getBounds().height));
		}
		final int height = getBounds().height - 2;
		graphics.setLineWidth(1);
		graphics.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());

		graphics.fillRoundRectangle(new Rectangle(x, y, width, height), GUIDefaults.COLLAPSED_DECORATOR_ARC_RADIUS, GUIDefaults.COLLAPSED_DECORATOR_ARC_RADIUS);
		graphics.drawRoundRectangle(new Rectangle(x, y, width, height), GUIDefaults.COLLAPSED_DECORATOR_ARC_RADIUS, GUIDefaults.COLLAPSED_DECORATOR_ARC_RADIUS);
	}

}
