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
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.Panel;
import org.eclipse.draw2d.ToolbarLayout;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.swt.graphics.Color;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IPropertyContainer;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramExtension;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIBasics;
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

		sourceAnchor = new SourceAnchor(this, feature);
		targetAnchor = new TargetAnchor(this, feature);

		setLayoutManager(layout);

		label.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		label.setFont(DEFAULT_FONT);

		label.setLocation(new Point(FEATURE_INSETS.left, FEATURE_INSETS.top));
		
		String displayName = feature.getObject().getName();
		if(featureModel.getLayout().showShortNames()){
			int lastIndexOf = displayName.lastIndexOf(".");
			displayName = displayName.substring(++lastIndexOf);
		}
		setName(displayName);

		setProperties();

		feature.setSize(getSize());

		add(label, label.getBounds());
		setOpaque(true);

		if (feature.getLocation() != null) {
			setLocation(feature.getLocation());
		}

		if (!featureModel.getLayout().showHiddenFeatures() && feature.getObject().getStructure().hasHiddenParent()) {
			setSize(new Dimension(0, 0));
		}
	}

	public void setProperties() {
		final StringBuilder toolTip = new StringBuilder();

		label.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		setBackgroundColor(FMPropertyManager.getConcreteFeatureBackgroundColor());
		setBorder(FMPropertyManager.getFeatureBorder(feature.isConstraintSelected()));

		IFeature feature = this.feature.getObject();
		List<String> explanation = new ArrayList<String>();
		final FeatureModelAnalyzer analyser = feature.getFeatureModel().getAnalyser();
		
		boolean hasExpl = false;
		if (feature.getProperty().getFeatureStatus() == FeatureStatus.DEAD || 
				feature.getProperty().getFeatureStatus() == FeatureStatus.FALSE_OPTIONAL || 
				feature.getStructure().isRoot() && !analyser.valid()) {
			hasExpl = true;
		}
		
		if (!FeatureColorManager.getCurrentColorScheme(feature).isDefault()) {
			// only color if the active profile is not the default profile
			FeatureColor color = FeatureColorManager.getColor(feature);
			if (color != FeatureColor.NO_COLOR) {
				setBackgroundColor(new Color(null, ColorPalette.getRGB(color.getValue(), 0.5f)));
			} else {
				if (feature.getStructure().isConcrete()) {
					toolTip.append(CONCRETE);
				} else {
					setBackgroundColor(FMPropertyManager.getAbstractFeatureBackgroundColor());
					toolTip.append(ABSTRACT);
				}
			}
		} else {
			if (feature.getStructure().isRoot() && !analyser.valid()) {
				setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
				setBorder(FMPropertyManager.getDeadFeatureBorder(this.feature.isConstraintSelected()));
				explanation = analyser.deadFeatureExpl.get(feature); // get explanation for void feature model
			//	toolTip.append(VOID);
			} else {
				if (feature.getStructure().isConcrete()) {
					if (!hasExpl) {
						toolTip.append(CONCRETE);
					}
				} else {
					setBackgroundColor(FMPropertyManager.getAbstractFeatureBackgroundColor());
					if (!hasExpl) {
						toolTip.append(ABSTRACT);
					}
				}

				if (feature.getStructure().hasHiddenParent()) {
					setBorder(FMPropertyManager.getHiddenFeatureBorder(this.feature.isConstraintSelected()));
					label.setForegroundColor(HIDDEN_FOREGROUND);
					toolTip.append(feature.getStructure().isHidden() ? HIDDEN : HIDDEN_PARENT);
				}

				if (!hasExpl) {
					toolTip.append(feature.getStructure().isRoot() ? ROOT : FEATURE);
				}

				switch (feature.getProperty().getFeatureStatus()) {
				case DEAD:
					if (analyser.valid()) {
						setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
						setBorder(FMPropertyManager.getDeadFeatureBorder(this.feature.isConstraintSelected()));
						explanation = analyser.deadFeatureExpl.get(feature); // get explanation for dead feature
					//	toolTip.append(DEAD);
					}
					break;
				case FALSE_OPTIONAL:
					setBackgroundColor(FMPropertyManager.getWarningColor());
					setBorder(FMPropertyManager.getConcreteFeatureBorder(this.feature.isConstraintSelected()));
					explanation = analyser.falseOptFeatureExpl.get(feature); // get explanation for false optional feature
			//		toolTip.append(FALSE_OPTIONAL);
					break;
				case INDETERMINATE_HIDDEN:
					setBackgroundColor(FMPropertyManager.getWarningColor());
					setBorder(FMPropertyManager.getHiddenFeatureBorder(this.feature.isConstraintSelected()));
					toolTip.append(INDETERMINATE_HIDDEN);
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
			String c = hasExpl? "\nConstraints:\n" : "\n\nConstraints:\n";
			toolTip.append(c);
			toolTip.append(contraints + "\n");
		}

		Figure toolTipContent = new Figure();
		toolTipContent.setLayoutManager(gl);

		if (!hasExpl) {
			Label featureName = new Label(feature.getName());
			featureName.setFont(DEFAULT_FONT_BOLD);
			toolTipContent.add(featureName);
		}
		Label furtherInfos = new Label(toolTip.toString());
		furtherInfos.setFont(DEFAULT_FONT);
		toolTipContent.add(furtherInfos);
		appendCustomProperties(toolTipContent);

		// call of the FeatureDiagramExtensions
		for (FeatureDiagramExtension extension : FeatureDiagramExtension.getExtensions()) {
			toolTipContent = extension.extendFeatureFigureToolTip(toolTipContent, this);
		}
		Panel panel = new Panel();
		panel.setLayoutManager(new ToolbarLayout(false));

		// only set explanation if not null or empty
		if (explanation == null) {
			setToolTip(toolTipContent);
		} else if (explanation.isEmpty()) {
			setToolTip(toolTipContent);
		} else {
			setToolTip(toolTipContent, panel, explanation);
		}
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

			for (int i = 0; i < size; i++) {
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

	/**
	 * Color explanation parts according to their occurrences in all explanations for a defect feature.
	 * If expl. part occured once, it is colored black. If it occurred in every explanation, it is colored red.
	 * For all other cases, a color gradient is used.
	 * 
	 * @param the origin content of a feature tool tip, i.e. feature name and respective constraints
	 * @param panel the panel to pass for a tool tip
	 * @param expl the explanation within a tool tip
	 */
	private void setToolTip(Figure content, Panel panel, List<String> expl) {
		for (String s : expl) {
			if (s.contains("$")) {
				int lastChar = s.lastIndexOf("$");
				String text = s.substring(0, lastChar); // pure explanation without delimiter and count of explanation part
				int occur = 1; //if non-negative, intersection, number of all occurences of expl. part
				int allExpl = 1; // number of all explanations
				if (lastChar < s.length() - 1) {
					String suffix = s.substring(lastChar + 1, s.length()); // 2 (occur) /3 (allExpl)
					String[] l = suffix.split("/");
					if (l.length == 2) {
						try {
							occur = Integer.parseInt(l[0]);
							allExpl = Integer.parseInt(l[1]);

						} catch (NumberFormatException e) {
							System.out.println(e);
						}
					}
				}
				//check validity
				if (allExpl < 1 || occur < 1 || occur > allExpl) {
					System.out.println("inconsistent suffix: " + occur + "/" + allExpl + ", use defaults 1/1");
					occur = 1;
					allExpl = 1;
				}
				//if we are here, occur and allExpl are both >=1 and occur <= allExpl - consistent!
				Label tmp = new Label(text + " (" + occur + "/" + allExpl + ")");
				if (allExpl == 1) {
					tmp.setForegroundColor(GUIBasics.createColor(255, 0, 0));
				} else { //allExp > 1, can divide through allExpl - 1 
					if (occur == 1)
						tmp.setForegroundColor(GUIBasics.createColor(0, 0, 0)); // black for explanation part which occurs once

					// color gradient for remaining explanations
					else {
						int confidence = (int) (255.0 * (occur - 1.0) / (allExpl - 1.0) + 0.5);
						tmp.setForegroundColor(GUIBasics.createColor(confidence, 0, 0));
					}
				}
				tmp.setFont(DEFAULT_FONT);
				panel.add(tmp);
			} else { // if we are here, we process the header of an explanation, i.e. feature x is dead, because
				Label tmp = new Label(s);
				tmp.setFont(DEFAULT_FONT_BOLD);
				panel.add(tmp);
			}
		}
		panel.add(content);
		setToolTip(panel);
	}

	public ConnectionAnchor getSourceAnchor() {
		return sourceAnchor;
	}

	public ConnectionAnchor getTargetAnchor() {
		return targetAnchor;
	}

	public void setName(String newName) {
		if (label.getText().equals(newName)) {
			return;
		}
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
