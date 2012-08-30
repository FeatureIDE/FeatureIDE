/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramExtension;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.anchors.SourceAnchor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.anchors.TargetAnchor;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;


/**
 * A figure that represents a feature with its name.
 * 
 * @author Thomas Thuem
 */
public class FeatureFigure extends Figure implements GUIDefaults {
	
	private final Label label = new Label();
	
	private static final FreeformLayout layout = new FreeformLayout();

	private final ConnectionAnchor sourceAnchor;
	
	private final ConnectionAnchor targetAnchor;

	private Feature feature;

	private FeatureModel featureModel;
	
	private static GridLayout gl = new GridLayout();
	
	private static String CONCRETE = " Concrete";
	private static String ABSTRACT = " Abstract";
	private static String HIDDEN = " hidden";
	private static String DEAD = "is dead ";
	private static String FEATURE = " feature ";
	private static String FALSE_OPTIONAL = "is false optional ";
	private static String INDETERMINATE_HIDDEN = "is hidden and indeterminate";
	private static String VOID = " Feature Model is void ";
	private static String ROOT = " Root ";

	public FeatureFigure(Feature feature, FeatureModel featureModel) {
		super();
		this.feature = feature;
		this.featureModel = featureModel;
		
		sourceAnchor = new SourceAnchor(this, feature);
		targetAnchor = new TargetAnchor(this, feature);
		
		setLayoutManager(layout);

		label.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		label.setFont(DEFAULT_FONT);

		label.setLocation(new Point(FEATURE_INSETS.left, FEATURE_INSETS.top));
		
		setName(feature.getName());

		setProperties();
		
		
		FeatureUIHelper.setSize(feature,getSize());
		
		add(label);
		setOpaque(true);

		if (FeatureUIHelper.getLocation(feature) != null)
			setLocation(FeatureUIHelper.getLocation(feature));
		
		if(isHidden(feature)){
			setSize(new Dimension(0,0));
		}
	}
	
	boolean isHidden(Feature feature){
		if(featureModel.getLayout().showHiddenFeatures()){
			return false;
		} else {
			if(feature.isHidden()){
				return true;
			}
			if(!feature.isRoot()){
				return isHidden(feature.getParent());
			} else {
				return feature.isHidden();
			}
		}

	}

	public void setProperties() {
	
		String toolTip = "";
		boolean modelIsValid = featureModel.valid();
		
		label.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		setBackgroundColor(FMPropertyManager.getConcreteFeatureBackgroundColor());
		setBorder(FMPropertyManager.getConcreteFeatureBorder(feature.isConstraintSelected()));
		
		if (feature.isConcrete()) toolTip += CONCRETE;
		
		if (feature.isAbstract()){
			setBackgroundColor(FMPropertyManager.getAbstractFeatureBackgroundColor());
			setBorder(FMPropertyManager.getAbsteactFeatureBorder(feature.isConstraintSelected()));
			if (feature.isRoot()){
				toolTip += ROOT;
			} else {
				toolTip += ABSTRACT;
			}
		}
		
		if (feature.hasHiddenParent()){
			setBorder(FMPropertyManager.getHiddenFeatureBorder(feature.isConstraintSelected()));
			label.setForegroundColor(HIDDEN_FOREGROUND);
			if (feature.isHidden()) toolTip += HIDDEN;
		}
		
		if (!feature.isRoot()) toolTip += FEATURE;
		
		if ((feature.getFeatureStatus() == FeatureStatus.DEAD) && modelIsValid){
			setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
			setBorder(FMPropertyManager.getDeadFeatureBorder(feature.isConstraintSelected()));
			toolTip += DEAD;			
		}
		
		if (feature.getFeatureStatus() == FeatureStatus.FALSE_OPTIONAL){
			setBackgroundColor(FMPropertyManager.getWarningColor());
			setBorder(FMPropertyManager.getConcreteFeatureBorder(feature.isConstraintSelected()));
			toolTip += FALSE_OPTIONAL;
		}
		
		if (feature.getFeatureStatus() == FeatureStatus.INDETERMINATE_HIDDEN){
			setBackgroundColor(FMPropertyManager.getWarningColor());
			setBorder(FMPropertyManager.getConcreteFeatureBorder(feature.isConstraintSelected()));
			toolTip += INDETERMINATE_HIDDEN;
		}
		
		if (feature.isRoot() && !modelIsValid){
			setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
			setBorder(FMPropertyManager.getDeadFeatureBorder(feature.isConstraintSelected()));
			toolTip = VOID;
		}
		
		toolTip += getRelevantConstraints();
		Figure toolTipContent = new Figure();
		toolTipContent.setLayoutManager(gl);
		toolTipContent.setFont(DEFAULT_FONT);
		toolTipContent.add(new Label(toolTip));
		
		// call of the FeatureDiagramExtensions
		for (FeatureDiagramExtension extension : FeatureDiagramExtension.getExtensions()) {
			toolTipContent = extension.extendFeatureFigureToolTip(toolTipContent, this);
		}
		
		setToolTip(toolTipContent);
	}
	
	private String getRelevantConstraints() {
		StringBuilder relevant = new StringBuilder();
		for (Constraint constraint : featureModel.getConstraints()) {
			String node = constraint.getNode().toString(NodeWriter.logicalSymbols);
			if (node.contains(feature.getName()))
				relevant.append("\n " + node + " ");
		}
		if (relevant.length() > 0) {
			return "\n" + relevant.toString();
		}
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
	
	/**
	 * @return The <code>Feature</code> represented by this <code>FeatureFigure</code>
	 */
	public Feature getFeature() {
		return feature;
	}
}
