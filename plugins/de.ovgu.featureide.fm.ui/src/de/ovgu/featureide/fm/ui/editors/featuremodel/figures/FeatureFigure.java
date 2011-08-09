/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.ConnectionAnchor;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.prop4j.NodeWriter;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.anchors.SourceAnchor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.anchors.TargetAnchor;


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

	private Feature feature;

	private FeatureModel featureModel;

	public FeatureFigure(Feature feature, FeatureModel featureModel) {
		super();
		this.feature = feature;
		this.featureModel = featureModel;
		
		sourceAnchor = new SourceAnchor(this, feature);
		targetAnchor = new TargetAnchor(this, feature);
		
		setLayoutManager(layout);

		label.setForegroundColor(FEATURE_FOREGROUND);
		label.setFont(DEFAULT_FONT);

		label.setLocation(new Point(FEATURE_INSETS.left, FEATURE_INSETS.top));
		
		setName(feature.getName());

		setProperties();
		
		
		FeatureUIHelper.setSize(feature,getSize());
		
		add(label);
		setOpaque(true);

		if (FeatureUIHelper.getLocation(feature) != null)
			setLocation(FeatureUIHelper.getLocation(feature));
	}
	
	public void setProperties() {
	
		String toolTip = "";
		
		setBackgroundColor(CONCRETE_BACKGROUND);
		setBorder(CONCRETE_BORDER);
		
		if (feature.isConcrete()) toolTip += " Concrete";
		
		if (feature.isAbstract()){
			setBackgroundColor(ABSTRACT_BACKGROUND);
			setBorder(ABSTRACT_BORDER);
			toolTip += " Abstract";
		}
		
		if (feature.isHidden()){
			setBorder(HIDDEN_BORDER);
			label.setForegroundColor(HIDDEN_FOREGROUND);
			toolTip += " Hidden";
		}
		
		if (feature.getFeatureStatus() == FeatureStatus.DEAD){
			label.setForegroundColor(DEAD_COLOR);
			setBorder(DEAD_BORDER);
			toolTip += " Dead";			
		}
		
		if (feature.getFeatureStatus() == FeatureStatus.FALSE_OPTIONAL){
			label.setForegroundColor(DEAD_COLOR);
			setBorder(DEAD_BORDER);
			toolTip += " False Optional";
		}
		
		try {
			if (feature.isRoot() && !featureModel.isValid()){
				label.setForegroundColor(DEAD_COLOR);
				setBorder(DEAD_BORDER);
				toolTip = " Void Model ";
			}
		} catch (TimeoutException e) {
			e.printStackTrace();
		}
		
		if (!feature.isRoot()) toolTip += " Feature ";
		
		toolTip += getRelevantConstraints();
		setToolTip(new Label(toolTip));
	}

	private String getRelevantConstraints() {
		String relevant = "";
		for (Constraint constraint : featureModel.getConstraints()) {
			String node = constraint.getNode().toString(NodeWriter.logicalSymbols);
			if (node.contains(feature.getName()))
				relevant += "\n " + node + " ";
		}
		if (!relevant.isEmpty())
			return "\n" + relevant;
		return "";
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
