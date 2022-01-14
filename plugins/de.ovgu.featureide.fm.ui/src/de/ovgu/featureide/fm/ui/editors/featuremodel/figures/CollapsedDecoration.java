/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import org.abego.treelayout.Configuration;
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
 * A decoration for a feature connection that indicates the collapsed property.
 *
 * @author Joshua Sprey
 * @author Enis Belli
 * @author Christopher Sontag
 * @author Maximilian Kühl
 * @author Insansa Michel
 * @author Malek Badeer
 * @author Martha Nyerembe
 * @author Lukas Vogt
 */
public class CollapsedDecoration extends ConnectionDecoration implements GUIDefaults {

	private final Label childrenCount = new Label();
	private static final FreeformLayout layout = new FreeformLayout();

	private IGraphicalFeature graphicalFeature;

	public boolean isLegendEntry = false;

	public CollapsedDecoration(IGraphicalFeature parent) {
		super();
		graphicalFeature = parent;
		setLayoutManager(layout);
		setBackgroundColor(FMPropertyManager.getDiagramBackgroundColor());
		setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		graphicalFeature.setCollapsedDecoration(this);

		childrenCount.setFont(DEFAULT_FONT);
		childrenCount.setLocation(new Point(0, 0));
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
		childrenCount.setLocation(new Point(0, 0));
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
			// Calculate layout direction
			final FeatureModelLayout layout = graphicalFeature.getGraphicalModel().getLayout();
			final Configuration.Location rootPosition = layout.isUsesAbegoTreeLayout() ? layout.getAbegoRootposition()
				: (layout.hasVerticalLayout() ? Configuration.Location.Left : Configuration.Location.Top);

			// Apply offset to center the decoration box along the appropriate edge of the graphical feature and take
			// GUIDefaults.COLLAPSED_DECORATOR_FEATURE_SPACE into account
			switch (rootPosition) {
			case Top:
				super.setLocation(p.translate(-getBounds().width / 2, GUIDefaults.COLLAPSED_DECORATOR_FEATURE_SPACE));
				break;
			case Left:
				super.setLocation(p.translate(GUIDefaults.COLLAPSED_DECORATOR_FEATURE_SPACE, -getBounds().height / 2));
				break;
			case Right:
				super.setLocation(p.translate(-getBounds().width - GUIDefaults.COLLAPSED_DECORATOR_FEATURE_SPACE, -getBounds().height / 2));
				break;
			case Bottom:
				super.setLocation(p.translate(-getBounds().width / 2, -getBounds().height - GUIDefaults.COLLAPSED_DECORATOR_FEATURE_SPACE));
				break;
			}
		}
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

		final Dimension labelSize = childrenCount.getTextBounds().getSize();
		labelSize.expand(GUIDefaults.COLLAPSED_DECORATOR_X_SPACE * 2, GUIDefaults.COLLAPSED_DECORATOR_Y_SPACE * 2);
		if (!labelSize.equals(childrenCount.getSize())) {
			childrenCount.setSize(labelSize);
			setSize(labelSize);
		}
	}

	@Override
	public void setReferencePoint(Point p) {}

	@Override
	protected void fillShape(Graphics graphics) {}

	@Override
	protected void outlineShape(Graphics graphics) {
		final Rectangle bounds = new Rectangle(getBounds()); // Create copy of bounds, so original bounds are not modified
		bounds.width--;
		bounds.height--;

		graphics.setLineWidth(1);
		graphics.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		graphics.fillRoundRectangle(bounds, GUIDefaults.COLLAPSED_DECORATOR_ARC_RADIUS, GUIDefaults.COLLAPSED_DECORATOR_ARC_RADIUS);
		graphics.drawRoundRectangle(bounds, GUIDefaults.COLLAPSED_DECORATOR_ARC_RADIUS, GUIDefaults.COLLAPSED_DECORATOR_ARC_RADIUS);
	}

	public void refresh() {
		setDecoratorText("" + GetAllChildren(graphicalFeature.getObject().getStructure()));
	}
}
