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

import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_A_TAUTOLOGY_AND_SHOULD_BE_REMOVED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_REDUNDANT_AND_COULD_BE_REMOVED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_UNSATISFIABLE_AND_MAKES_THE_FEATURE_MODEL_VOID_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_MAKES_THE_FEATURE_MODEL_VOID_;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.analysis.ConstraintProperties;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.functional.Functional;
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

	public final static String VOID_MODEL = CONSTRAINT_MAKES_THE_FEATURE_MODEL_VOID_;
	public final static String UNSATISFIABLE = CONSTRAINT_IS_UNSATISFIABLE_AND_MAKES_THE_FEATURE_MODEL_VOID_;
	public final static String TAUTOLOGY = CONSTRAINT_IS_A_TAUTOLOGY_AND_SHOULD_BE_REMOVED_;
	public final static String DEAD_FEATURE = " Constraint makes following features dead: ";
	public final static String FALSE_OPTIONAL = " Constraint makes following features false optional: ";
	public final static String REDUNDANCE = CONSTRAINT_IS_REDUNDANT_AND_COULD_BE_REMOVED_;

	private static final IFigure VOID_LABEL = new Label(VOID_MODEL);
	private static final IFigure UNSATISFIABLE_LABEL = new Label(UNSATISFIABLE);
	private static final IFigure TAUTOLOGY_LABEL = new Label(TAUTOLOGY);
	private static final IFigure REDUNDANCE_LABEL = new Label(REDUNDANCE);

	private static final String[] symbols;
	static {
		if (GUIBasics.unicodeStringTest(DEFAULT_FONT, Arrays.toString(NodeWriter.logicalSymbols))) {
			symbols = NodeWriter.logicalSymbols;
		} else {
			symbols = NodeWriter.shortSymbols;
		}
	}

	private final Label label = new Label();

	private IGraphicalConstraint graphicalConstraint;

	public ConstraintFigure(IGraphicalConstraint constraint) {
		super();
		this.graphicalConstraint = constraint;
		setLayoutManager(new FreeformLayout());

		label.setForegroundColor(CONSTRAINT_FOREGROUND);
		label.setFont(DEFAULT_FONT);
		label.setLocation(new Point(CONSTRAINT_INSETS.left, CONSTRAINT_INSETS.top));

		setText(getConstraintText(constraint.getObject()));

		constraint.setSize(getSize());

		add(label);
		setOpaque(true);

		if (constraint.getLocation() != null)
			setLocation(constraint.getLocation());

		init();
	}

	private void init() {
		setText(getConstraintText(graphicalConstraint.getObject()));

		setBorder(FMPropertyManager.getConstraintBorder(graphicalConstraint.isFeatureSelected()));
		setToolTip(null);
		setBackgroundColor(FMPropertyManager.getConstraintBackgroundColor());
	}

	/**
	 * Sets the properties <i>color, border and tooltips</i> of the {@link ConstraintFigure}.
	 */
	public void setConstraintProperties() {
		init();

		final ConstraintProperties constraintProperties = FeatureUtils.getConstraintProperties(this.graphicalConstraint.getObject());
		final StringBuilder toolTip = new StringBuilder();

		switch (constraintProperties.getConstraintSatisfiabilityStatus()) {
		case SATISFIABLE:
			break;
		case VOID_MODEL:
			toolTip.append(VOID_LABEL);
			break;
		case UNSATISFIABLE:
			toolTip.append(UNSATISFIABLE_LABEL);
			break;
		default:
			break;
		}

		switch (constraintProperties.getConstraintDeadStatus()) {
		case NORMAL:
			break;
		case DEAD:
			if (!constraintProperties.getDeadFeatures().isEmpty()) {
				toolTip.append(DEAD_FEATURE);
				final List<String> deadFeatures = Functional.mapToList(constraintProperties.getDeadFeatures(), new Functional.ToStringFunction<IFeature>());
				Collections.sort(deadFeatures, String.CASE_INSENSITIVE_ORDER);

				for (String dead : deadFeatures) {
					toolTip.append("\n   ");
					toolTip.append(dead);
				}
			}
			break;
		default:
			break;
		}

		switch (constraintProperties.getConstraintFalseOptionalStatus()) {
		case NORMAL:
			break;
		case FALSE_OPTIONAL:
			if (!constraintProperties.getFalseOptionalFeatures().isEmpty()) {
				if (!constraintProperties.getDeadFeatures().isEmpty()) {
					toolTip.append("\n\n");
				}
				final List<String> falseOptionalFeatures = Functional.mapToList(constraintProperties.getFalseOptionalFeatures(),
						new Functional.ToStringFunction<IFeature>());
				Collections.sort(falseOptionalFeatures, String.CASE_INSENSITIVE_ORDER);

				toolTip.append(FALSE_OPTIONAL);
				for (String feature : falseOptionalFeatures) {
					toolTip.append("\n   ");
					toolTip.append(feature);
				}
			}
			break;
		default:
			break;
		}

		switch (constraintProperties.getConstraintRedundancyStatus()) {
		case NORMAL:
			break;
		case TAUTOLOGY:
			setBackgroundColor(FMPropertyManager.getWarningColor());
			toolTip.append(TAUTOLOGY_LABEL);
			break;
		case REDUNDANT:
		case IMPLICIT:
			setBackgroundColor(FMPropertyManager.getWarningColor());
			toolTip.append(REDUNDANCE_LABEL);
			break;
		default:
			break;
		}

		setToolTip(new Label(toolTip.toString()));

		if (getActiveReason() != null) {
			setBorder(FMPropertyManager.getReasonBorder(getActiveReason()));
		}
	}

	private String getConstraintText(IConstraint constraint) {
		return constraint.getNode().toString(symbols);
	}

	private void setText(String newText) {
		label.setText(newText);
		Dimension labelSize = label.getPreferredSize();

		if (labelSize.equals(label.getSize()))
			return;
		label.setSize(labelSize);

		Rectangle bounds = getBounds();
		int w = CONSTRAINT_INSETS.getWidth();
		int h = CONSTRAINT_INSETS.getHeight();
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

	@Override
	public ModelFigure getParent() {
		return (ModelFigure) super.getParent();
	}
}
