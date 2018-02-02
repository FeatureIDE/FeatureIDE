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

import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_A_TAUTOLOGY_AND_SHOULD_BE_REMOVED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_REDUNDANT_AND_COULD_BE_REMOVED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_UNSATISFIABLE_AND_MAKES_THE_FEATURE_MODEL_VOID_;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.explanations.ExplanationWriter;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIBasics;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * A figure to view a cross-tree constraint below the feature diagram.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class ConstraintFigure extends ModelElementFigure implements GUIDefaults {

	public final static String VOID_MODEL = StringTable.FEATURE_MODELIS_VOID;
	public final static String UNSATISFIABLE = CONSTRAINT_IS_UNSATISFIABLE_AND_MAKES_THE_FEATURE_MODEL_VOID_;
	public final static String TAUTOLOGY = CONSTRAINT_IS_A_TAUTOLOGY_AND_SHOULD_BE_REMOVED_;
	public final static String DEAD_FEATURE = "Constraint makes following features dead:";
	public final static String FALSE_OPTIONAL = "Constraint makes following features false-optional:";
	public final static String REDUNDANCE = CONSTRAINT_IS_REDUNDANT_AND_COULD_BE_REMOVED_;

	private static final String[] symbols;
	static {
		if (GUIBasics.unicodeStringTest(DEFAULT_FONT, Arrays.toString(NodeWriter.logicalSymbols))) {
			symbols = NodeWriter.logicalSymbols;
		} else {
			symbols = NodeWriter.shortSymbols;
		}
	}

	private final Label label = new Label();

	private final IGraphicalConstraint graphicalConstraint;

	public ConstraintFigure(IGraphicalConstraint constraint) {
		super();
		graphicalConstraint = constraint;
		setLayoutManager(new FreeformLayout());

		label.setForegroundColor(CONSTRAINT_FOREGROUND);
		label.setFont(DEFAULT_FONT);
		label.setLocation(new Point(CONSTRAINT_INSETS.left, CONSTRAINT_INSETS.top));

		setText(getConstraintText(constraint.getObject()));

		constraint.setSize(getSize());

		add(label);
		setOpaque(true);

		if (constraint.getLocation() != null) {
			setLocation(constraint.getLocation());
		}

		init();
	}

	private void init() {
		setText(getConstraintText(graphicalConstraint.getObject()));
		setBorder(FMPropertyManager.getConstraintBorder(graphicalConstraint.isFeatureSelected()));
		setToolTip(null);
		setBackgroundColor(FMPropertyManager.getConstraintBackgroundColor());
	}

	/**
	 * Sets the properties <i>icon, border and tooltips</i> of the {@link ConstraintFigure}.
	 */
	public void setConstraintProperties() {
		init();

		final IConstraint constraint = graphicalConstraint.getObject();

		final IFigure toolTipContent = new Figure();
		toolTipContent.setLayoutManager(new GridLayout());

		switch (constraint.getConstraintAttribute()) {
		case NORMAL:
			label.setIcon(null);
			break;
		case VOID_MODEL:
			label.setIcon(null);
			add(label);
			toolTipContent.add(new Label(VOID_MODEL));
			break;
		case UNSATISFIABLE:
			label.setIcon(null);
			toolTipContent.add(new Label(UNSATISFIABLE));
			break;
		case TAUTOLOGY:
			label.setIcon(null);
			add(label);
			toolTipContent.add(new Label(TAUTOLOGY));
			break;
		case REDUNDANT:
		case IMPLICIT:
			label.setIcon(FM_INFO);
			add(label);
			toolTipContent.add(new Label(REDUNDANCE));
			break;
		case DEAD:
			if (!constraint.getDeadFeatures().isEmpty()) {
				label.setIcon(null);
				final List<String> deadFeatures = new ArrayList<String>(constraint.getDeadFeatures().size());
				for (final IFeature dead : constraint.getDeadFeatures()) {
					deadFeatures.add(dead.toString());
				}
				Collections.sort(deadFeatures, String.CASE_INSENSITIVE_ORDER);

				String s = DEAD_FEATURE;
				for (final String dead : deadFeatures) {
					s += "\n\u2022 " + dead;
				}
				toolTipContent.add(new Label(s));
			}
			break;
		case FALSE_OPTIONAL:
			if (!constraint.getFalseOptional().isEmpty()) {
				label.setIcon(null);
				final List<String> falseOptionalFeatures = new ArrayList<String>(constraint.getFalseOptional().size());
				for (final IFeature feature : constraint.getFalseOptional()) {
					falseOptionalFeatures.add(feature.toString());
				}
				Collections.sort(falseOptionalFeatures, String.CASE_INSENSITIVE_ORDER);

				String s = FALSE_OPTIONAL;
				for (final String feature : falseOptionalFeatures) {
					s += "\n\u2022 " + feature;
				}
				toolTipContent.add(new Label(s));
			}
			break;
		default:
			break;
		}

		final String description = constraint.getDescription();
		if ((description != null) && !description.trim().isEmpty()) {
			toolTipContent.add(new Label("Description:"));
			toolTipContent.add(new Label(description));
		} else {
			toolTipContent.add(new Label("No Description"));
		}

		if (getActiveReason() != null) {
			add(label);

			setBorder(FMPropertyManager.getReasonBorder(getActiveReason()));
			final ExplanationWriter<?> w = getActiveReason().getExplanation().getWriter();
			String explanationString = "This constraint is involved in the selected defect:";
			explanationString += w.getReasonsString(Collections.singleton(getActiveReason()));
			toolTipContent.add(new Label(explanationString));
		}

		if (!toolTipContent.getChildren().isEmpty()) {
			setToolTip(toolTipContent);
		}

		setText(label.getText());
	}

	private String getConstraintText(IConstraint constraint) {
		return constraint.getNode().toString(symbols);
	}

	/**
	 * Sets the <i>text</i> and the <i>size</i> of the bounds of the {@link ConstraintFigure} with respect to the text and icon
	 */
	private void setText(String newText) {
		label.setText(newText);
		final Dimension labelSize = new Dimension(label.getPreferredSize());
		label.setSize(labelSize);

		final int w = CONSTRAINT_INSETS.getWidth();
		final int h = CONSTRAINT_INSETS.getHeight();
		setSize(labelSize.expand(w, h));

	}

	public Rectangle getLabelBounds() {
		return label.getBounds();
	}

	@Override
	public ModelFigure getParent() {
		return (ModelFigure) super.getParent();
	}
}
