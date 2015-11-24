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

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

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

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer.Attribute;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IPropertyContainer;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramExtension;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.anchors.SourceAnchor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.figures.anchors.TargetAnchor;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * A figure that represents a feature with its name.
 * 
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class FeatureFigure extends Figure implements GUIDefaults {

	private static final FreeformLayout layout = new FreeformLayout();

	private final Label label = new Label();

	private final ConnectionAnchor sourceAnchor;
	private final ConnectionAnchor targetAnchor;

	private IGraphicalFeature feature;

	private static GridLayout gl = new GridLayout();

	private static String ABSTRACT = " Abstract";
	private static String HIDDEN = " hidden";
	private static String HIDDEN_PARENT = INHERITED_HIDDEN;
	private static String DEAD = IS_DEAD;
	private static String FEATURE = " feature ";
	private static String FALSE_OPTIONAL = IS_FALSE_OPTIONAL;
	private static String INDETERMINATE_HIDDEN = IS_HIDDEN_AND_INDETERMINATE;
	private static String VOID = FEATURE_MODEL_IS_VOID;

	public FeatureFigure(IGraphicalFeature feature, IGraphicalFeatureModel featureModel) {
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

		setName(feature.getObject().getName());

		setProperties();

		enforceLabelSize();
		FeatureUIHelper.setSize(feature, getSize());

		add(label, label.getBounds());
		setOpaque(true);

		if (FeatureUIHelper.getLocation(feature) != null) {
			setLocation(FeatureUIHelper.getLocation(feature));
		}

		if (!featureModel.getLayout().showHiddenFeatures() && feature.getObject().getStructure().hasHiddenParent()) {
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

	public void setProperties() {
		final StringBuilder toolTip = new StringBuilder();

		label.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		setBackgroundColor(FMPropertyManager.getConcreteFeatureBackgroundColor());
		setBorder(FMPropertyManager.getFeatureBorder(feature.isConstraintSelected()));
		
		IFeature feature = this.feature.getObject();

		final FeatureModelAnalyzer analyser = feature.getFeatureModel().getAnalyser();
		if (!FeatureColorManager.getCurrentColorScheme(feature).isDefault()) {
			// only color if the active profile is not the default profile
			FeatureColor color = FeatureColorManager.getColor(feature);
			if (color != FeatureColor.NO_COLOR) {
				setBackgroundColor(new Color(null, ColorPalette.getRGB(color.getValue(), 0.5f)));
			} else {
				if (feature.getStructure().isConcrete()) {
					toolTip.append(CONCRETE);
					analyser.setAttributeFlag(Attribute.Concrete, true);
				} else {
					setBackgroundColor(FMPropertyManager.getAbstractFeatureBackgroundColor());
					toolTip.append(ABSTRACT);
					analyser.setAttributeFlag(Attribute.Abstract, true);
				}
			}
		} else {
			if (feature.getStructure().isRoot() && !analyser.valid()) {
				setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
				setBorder(FMPropertyManager.getDeadFeatureBorder(feature.isConstraintSelected()));
				toolTip.append(VOID);
			} else {
				if (feature.getStructure().isConcrete()) {
					toolTip.append(CONCRETE);
					analyser.setAttributeFlag(Attribute.Concrete, true);
				} else {
					setBackgroundColor(FMPropertyManager.getAbstractFeatureBackgroundColor());
					toolTip.append(ABSTRACT);
					analyser.setAttributeFlag(Attribute.Abstract, true);
				}

				if (feature.getStructure().hasHiddenParent()) {
					setBorder(FMPropertyManager.getHiddenFeatureBorder(feature.isConstraintSelected()));
					label.setForegroundColor(HIDDEN_FOREGROUND);
					toolTip.append(feature.getStructure().isHidden() ? HIDDEN : HIDDEN_PARENT);
					analyser.setAttributeFlag(Attribute.Hidden, true);
				}

				toolTip.append(feature.getStructure().isRoot() ? ROOT : FEATURE);

				switch (feature.getProperty().getFeatureStatus()) {
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

		final String description = feature.getProperty().getDescription();
		if (description != null && !description.trim().isEmpty()) {
			toolTip.append("\n\nDescription:\n");
			toolTip.append(description);
		}

		final String contraints = FeatureUtils.getRelevantConstraintsString(feature);
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
		appendCustomProperties(toolTipContent);

		// call of the FeatureDiagramExtensions
		for (FeatureDiagramExtension extension : FeatureDiagramExtension.getExtensions()) {
			toolTipContent = extension.extendFeatureFigureToolTip(toolTipContent, this);
		}
		
		setToolTip(toolTipContent);
	}

	private void appendCustomProperties(Figure toolTipContent) {
		StringBuilder sb = new StringBuilder();
		final IPropertyContainer props = feature.getObject().getCustomProperties();
		final List<String> keys = new ArrayList<>(props.keySet());
		Collections.sort(keys);
		if (!keys.isEmpty()) {
			int size = props.keySet().size();
			int maxKeyLength = 0;
			for (int i = 0; i < size; i++)
				maxKeyLength = Math.max(maxKeyLength, keys.get(i).length());
			
			for(int i = 0; i < size; i++) {
				final String key = keys.get(i);
				sb.append(String.format("  %1$-" + maxKeyLength + "s", key));
				sb.append("\t=\t");
				sb.append(props.get(key));
				if (i + 1 < size)
					sb.append("\n");
			}
			
			Label propertiesInfo = new Label("\nCustom Properties");
			propertiesInfo.setFont(DEFAULT_FONT_BOLD);
			Label properties = new Label(sb.toString());
			properties.setFont(DEFAULT_FONT);
			
			
			toolTipContent.add(propertiesInfo);
			toolTipContent.add(properties);
		}
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
	public IGraphicalFeature getFeature() {
		return feature;
	}
}
