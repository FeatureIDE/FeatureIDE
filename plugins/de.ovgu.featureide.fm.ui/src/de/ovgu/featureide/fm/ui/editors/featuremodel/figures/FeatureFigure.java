/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.CONCRETE;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_MODEL_IS_VOID;
import static de.ovgu.featureide.fm.core.localization.StringTable.INHERITED_HIDDEN;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_DEAD;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_FALSE_OPTIONAL;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_HIDDEN_AND_INDETERMINATE;
import static de.ovgu.featureide.fm.core.localization.StringTable.ROOT;

import org.eclipse.draw2d.ConnectionAnchor;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.editparts.ZoomListener;
import org.eclipse.swt.graphics.Color;

import de.ovgu.featureide.fm.core.ExtendedFeature;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer.Attribute;
import de.ovgu.featureide.fm.core.ProfileManager;
import de.ovgu.featureide.fm.core.ProfileManager.Project.Profile;
import de.ovgu.featureide.fm.core.annotation.ColorPalette;
import de.ovgu.featureide.fm.ui.PlugInProfileSerializer;
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

	private static final FreeformLayout layout = new FreeformLayout();

	private final Label label = new Label();

	private final ConnectionAnchor sourceAnchor;
	private final ConnectionAnchor targetAnchor;

	private Feature feature;

	private static GridLayout gl = new GridLayout();

	private static String ABSTRACT = " Abstract";
	private static String HIDDEN = " hidden";
	private static String HIDDEN_PARENT = INHERITED_HIDDEN;
	private static String DEAD = IS_DEAD;
	private static String FEATURE = " feature ";
	private static String FALSE_OPTIONAL = IS_FALSE_OPTIONAL;
	private static String INDETERMINATE_HIDDEN = IS_HIDDEN_AND_INDETERMINATE;
	private static String VOID = FEATURE_MODEL_IS_VOID;

	public FeatureFigure(Feature feature, FeatureModel featureModel) {
		super();
		this.feature = feature;

		FeatureUIHelper.getZoomManager().addZoomListener(new ZoomListener() {
			@Override
			public void zoomChanged(double arg0) {
				enforceLabelSize();
			}
		});

		sourceAnchor = new SourceAnchor(this, feature);
		targetAnchor = new TargetAnchor(this, feature);

		setLayoutManager(layout);

		label.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		label.setFont(DEFAULT_FONT);

		label.setLocation(new Point(FEATURE_INSETS.left, FEATURE_INSETS.top));

		setName(feature.getDisplayName());

		setProperties();

		enforceLabelSize();
		FeatureUIHelper.setSize(feature, getSize());

		add(label, label.getBounds());
		setOpaque(true);

		if (FeatureUIHelper.getLocation(feature) != null) {
			setLocation(FeatureUIHelper.getLocation(feature));
		}

		if (isHidden(feature)) {
			setSize(new Dimension(0, 0));
		}
	}

	/**
	 * After resizing this method ensures that label text will not be cut
	 * off(Issue #138)
	 */
	protected void enforceLabelSize() {
		if (!getChildren().isEmpty()) {
			setConstraint((IFigure) getChildren().get(0), label.getBounds().getExpanded(5, 0));
		}
	}

	private boolean isHidden(Feature feature) {
		return !feature.getFeatureModel().getLayout().showHiddenFeatures() && feature.hasHiddenParent();
	}

	/**
	 * @author Marcus Pinnecke
	 */
	//TODO: outsource method to global state

	private Profile getCurrentProfile(FeatureModel featureModel) {
		return ProfileManager.getProject(featureModel.xxxGetEclipseProjectPath(), PlugInProfileSerializer.FEATURE_PROJECT_SERIALIZER).getActiveProfile();
	}

	public void setProperties() {
		final StringBuilder toolTip = new StringBuilder();

		label.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		setBackgroundColor(FMPropertyManager.getConcreteFeatureBackgroundColor());
		setBorder(FMPropertyManager.getFeatureBorder(feature.isConstraintSelected()));

		// only color if the active profile is not the default profile
		if (ProfileManager.toColorIndex(getCurrentProfile(feature.getFeatureModel()).getColor(feature.getName())) != -1) {
			if (getCurrentProfile(feature.getFeatureModel()).hasFeatureColor(feature.getName())) {
				setBackgroundColor(new Color(null, ColorPalette.getRGB(
						ProfileManager.toColorIndex(getCurrentProfile(feature.getFeatureModel()).getColor(feature.getName())), 0.5f)));
			}
		} else {
			final FeatureModelAnalyzer analyser = feature.getFeatureModel().getAnalyser();
			if (feature.isRoot() && !analyser.valid()) {
				setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
				setBorder(FMPropertyManager.getDeadFeatureBorder(feature.isConstraintSelected()));
				toolTip.append(VOID);
			} else {
				if (feature.isConcrete()) {
					toolTip.append(CONCRETE);
					analyser.setAttributeFlag(Attribute.Concrete, true);
				} else {
					setBackgroundColor(FMPropertyManager.getAbstractFeatureBackgroundColor());
					toolTip.append(ABSTRACT);
					analyser.setAttributeFlag(Attribute.Abstract, true);
				}

				if (feature.hasHiddenParent()) {
					setBorder(FMPropertyManager.getHiddenFeatureBorder(feature.isConstraintSelected()));
					label.setForegroundColor(HIDDEN_FOREGROUND);
					toolTip.append(feature.isHidden() ? HIDDEN : HIDDEN_PARENT);
					analyser.setAttributeFlag(Attribute.Hidden, true);
				}

				toolTip.append(feature.isRoot() ? ROOT : FEATURE);

				switch (feature.getFeatureStatus()) {
				case DEAD:
					if (analyser.valid()) {
						setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
						setBorder(FMPropertyManager.getDeadFeatureBorder(feature.isConstraintSelected()));
						toolTip.append(DEAD);
						analyser.setAttributeFlag(Attribute.Dead, true);
					}
					break;
				case FALSE_OPTIONAL:
					setBackgroundColor(FMPropertyManager.getWarningColor());
					setBorder(FMPropertyManager.getConcreteFeatureBorder(feature.isConstraintSelected()));
					toolTip.append(FALSE_OPTIONAL);
					analyser.setAttributeFlag(Attribute.FalseOptional, true);
					break;
				case INDETERMINATE_HIDDEN:
					setBackgroundColor(FMPropertyManager.getWarningColor());
					setBorder(FMPropertyManager.getHiddenFeatureBorder(feature.isConstraintSelected()));
					toolTip.append(INDETERMINATE_HIDDEN);
					analyser.setAttributeFlag(Attribute.IndetHidden, true);
					break;
				default:
					break;
				}
			}
		}

		if (feature instanceof ExtendedFeature) {
			final ExtendedFeature extendedFeature = (ExtendedFeature) feature;

			if (extendedFeature.isInstance()) {
				setBorder(FMPropertyManager.getImportedFeatureBorder());
			}

			if (extendedFeature.isInherited()) {
				setBorder(FMPropertyManager.getInheritedFeatureBorder());
			}

			if (extendedFeature.isInterface()) {
				setBorder(FMPropertyManager.getInterfacedFeatureBorder());
			}
		}

		final String description = feature.getDescription();
		if (description != null && !description.trim().isEmpty()) {
			toolTip.append("\n\nDescription:\n");
			toolTip.append(description);
		}

		final String contraints = feature.getRelevantConstraintsString();
		if (!contraints.isEmpty()) {
			toolTip.append("\n\nConstraints:\n");
			toolTip.append(contraints);
		}

		Figure toolTipContent = new Figure();
		toolTipContent.setLayoutManager(gl);
		Label featureName = new Label(feature.getName());
		featureName.setFont(DEFAULT_FONT_BOLD);
		Label furtherInfos = new Label(toolTip.toString());
		furtherInfos.setFont(DEFAULT_FONT);
		toolTipContent.add(featureName);
		toolTipContent.add(furtherInfos);

		// call of the FeatureDiagramExtensions
		for (FeatureDiagramExtension extension : FeatureDiagramExtension.getExtensions()) {
			toolTipContent = extension.extendFeatureFigureToolTip(toolTipContent, this);
		}

		setToolTip(toolTipContent);
	}

	public ConnectionAnchor getSourceAnchor() {
		return sourceAnchor;
	}

	public ConnectionAnchor getTargetAnchor() {
		return targetAnchor;
	}

	public void setName(String newName) {
		label.setText(newName);

		final Dimension labelSize = label.getPreferredSize();
		this.minSize = labelSize;

		if (!labelSize.equals(label.getSize())) {
			label.setSize(labelSize);

			final Rectangle bounds = getBounds();
			bounds.setSize(labelSize.expand(FEATURE_INSETS.getWidth(), FEATURE_INSETS.getHeight()));

			final Dimension oldSize = getSize();
			if (!oldSize.equals(0, 0)) {
				bounds.x += (oldSize.width - bounds.width) >> 1;
			}

			setBounds(bounds);
		}
	}

	public Rectangle getLabelBounds() {
		return label.getBounds();
	}

	/**
	 * @return The {@link Feature} represented by this {@link FeatureFigure}
	 */
	public Feature getFeature() {
		return feature;
	}
}
