/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.ConnectionAnchor;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import featureide.fm.core.Feature;
import featureide.fm.ui.editors.FeatureUIHelper;
import featureide.fm.ui.editors.featuremodel.GUIDefaults;
import featureide.fm.ui.editors.featuremodel.figures.anchors.SourceAnchor;
import featureide.fm.ui.editors.featuremodel.figures.anchors.TargetAnchor;

/**
 * A figure that represents a feature with its name.
 * 
 * @author Thomas Thuem
 */
public class FeatureFigure extends Figure implements GUIDefaults {
	
	private final Label label = new Label();
	
	private final FreeformLayout layout = new FreeformLayout();

	private final ConnectionAnchor sourceAnchor;
	
	private final ConnectionAnchor targetAnchor;

	public FeatureFigure(Feature feature) {
		super();
		
		sourceAnchor = new SourceAnchor(this, feature);
		targetAnchor = new TargetAnchor(this, feature);
		
		setLayoutManager(layout);

		label.setForegroundColor(FEATURE_FOREGROUND);
		label.setFont(DEFAULT_FONT);

		label.setLocation(new Point(FEATURE_INSETS.left, FEATURE_INSETS.top));
		
		setName(feature.getName());
		setAbstract(feature.isAbstract());

		FeatureUIHelper.setSize(feature,getSize());
		
		add(label);
		setOpaque(true);

		if (FeatureUIHelper.getLocation(feature) != null)
			setLocation(FeatureUIHelper.getLocation(feature));
	}
	
	public void setAbstract(boolean compound) {
		setBorder(compound ? COMPOUND_BORDER : LAYER_BORDER);
		setBackgroundColor(compound ? COMPOUND_BACKGROUND : LAYER_BACKGROUND);
		
		String toolTip = compound ? "Compound Feature" : "Layer (Feature)";
		setToolTip(new Label(toolTip));
	}

	public ConnectionAnchor getSourceAnchor() {
		return sourceAnchor;
	}

	public ConnectionAnchor getTargetAnchor() {
		return targetAnchor;
	}

	public void setName(String newName) {
		label.setText(newName);
		Dimension labelSize = label.getPreferredSize();
		
		if (labelSize.equals(label.getSize()))
			return;
		label.setSize(labelSize);

		Rectangle bounds = getBounds();
		int w = FEATURE_INSETS.getWidth();
		int h = FEATURE_INSETS.getHeight();
		bounds.setSize(labelSize.expand(w, h));

		Dimension oldSize = getSize();
		if (!oldSize.equals(0, 0)) {
			int dx = (oldSize.width - bounds.width) / 2;
			bounds.x += dx;
		}

		setBounds(bounds);
	}

	public Rectangle getLabelBounds() {
		return label.getBounds();
	}
	
}
