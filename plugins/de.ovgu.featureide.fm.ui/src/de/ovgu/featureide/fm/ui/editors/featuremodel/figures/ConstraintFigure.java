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

import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_A_TAUTOLOGY_AND_SHOULD_BE_REMOVED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_REDUNDANT_AND_COULD_BE_REMOVED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_UNSATISFIABLE_AND_MAKES_THE_FEATURE_MODEL_VOID_;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.analysis.ConstraintProperties;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintStatus;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelProperty;
import de.ovgu.featureide.fm.core.explanations.ExplanationWriter;
import de.ovgu.featureide.fm.core.functional.Functional;
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
		label.setLocation(new Point(0, 0));

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
	@Override
	public void updateProperties() {
		init();

		final IFigure toolTipContent = new Figure();
		toolTipContent.setLayoutManager(new GridLayout());

		// Check if automatic calculations are nessecary (propetries are only available when anaylses are activated)
		if (FeatureModelProperty.isRunCalculationAutomatically(graphicalConstraint.getGraphicalModel().getFeatureModelManager().getVarObject())
			&& FeatureModelProperty.isCalculateFeatures(graphicalConstraint.getGraphicalModel().getFeatureModelManager().getVarObject())
			&& FeatureModelProperty.isCalculateConstraints(graphicalConstraint.getGraphicalModel().getFeatureModelManager().getVarObject())) {
			final ConstraintProperties constraintProperties = graphicalConstraint.getGraphicalModel().getFeatureModelManager().getVariableFormula()
					.getAnalyzer().getAnalysesCollection().getConstraintProperty(graphicalConstraint.getObject());

			if (constraintProperties.hasStatus(ConstraintStatus.SATISFIABLE)) {
				label.setIcon(null);
			} else if (constraintProperties.hasStatus(ConstraintStatus.VOID)) {
				label.setIcon(FM_ERROR);
				add(label);
				toolTipContent.add(new Label(VOID_MODEL));
			} else if (constraintProperties.hasStatus(ConstraintStatus.UNSATISFIABLE)) {
				label.setIcon(FM_ERROR);
				toolTipContent.add(new Label(UNSATISFIABLE));
			}

			if (constraintProperties.hasStatus(ConstraintStatus.TAUTOLOGY)) {
				label.setIcon(FM_WARNING);
				add(label);
				toolTipContent.add(new Label(TAUTOLOGY));
			} else if (constraintProperties.hasStatus(ConstraintStatus.REDUNDANT)) {
				label.setIcon(FM_INFO);
				add(label);
				toolTipContent.add(new Label(REDUNDANCE));
			} else if (constraintProperties.hasStatus(ConstraintStatus.IMPLICIT)) {
				setBorder(new LineBorder(GUIDefaults.IMPLICIT_CONSTRAINT, 3));
				setBackgroundColor(FMPropertyManager.getWarningColor());
				add(label);
				toolTipContent.add(new Label(REDUNDANCE));
			}

			if (!constraintProperties.getDeadFeatures().isEmpty()) {
				final List<String> deadFeatures = Functional.mapToList(constraintProperties.getDeadFeatures(), new Functional.ToStringFunction<IFeature>());
				Collections.sort(deadFeatures, String.CASE_INSENSITIVE_ORDER);

				String s = DEAD_FEATURE;
				for (final String dead : deadFeatures) {
					s += "\n\u2022 " + dead;
				}
				toolTipContent.add(new Label(s));
			}

			if (!constraintProperties.getFalseOptionalFeatures().isEmpty()) {
				final List<String> falseOptionalFeatures =
					Functional.mapToList(constraintProperties.getFalseOptionalFeatures(), new Functional.ToStringFunction<IFeature>());
				Collections.sort(falseOptionalFeatures, String.CASE_INSENSITIVE_ORDER);

				String s = FALSE_OPTIONAL;
				for (final String feature : falseOptionalFeatures) {
					s += "\n\u2022 " + feature;
				}
				toolTipContent.add(new Label(s));
			}
		}

		final String description = graphicalConstraint.getObject().getDescription();
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

	/**
	 * Returns the text this figure should show for the given constraint. This text might have long or short feature names (though constraint remains
	 * unchanged).
	 *
	 * @param constraint - {@link IConstraint}
	 * @return {@link String}
	 */
	private String getConstraintText(IConstraint constraint) {
		Node node = constraint.getNode();
		if (graphicalConstraint.getGraphicalModel().getLayout().showShortNames()) {
			node = rewriteShortLabels(node);
		}
		return node.toString(symbols);
	}

	/**
	 * Rewrites the given formula represented by node into a new one that has the correct-length feature names to display. node remains unchanged.
	 *
	 * @param node - {@link Node}
	 * @return new {@link Node}
	 */
	private Node rewriteShortLabels(Node node) {
		// Rewrite feature names for literal nodes.
		if (node instanceof Literal) {
			final String oldName = ((Literal) node).var.toString();
			int lastIndexOf = oldName.lastIndexOf(".");
			final String newName = oldName.substring(++lastIndexOf);
			return new Literal(newName, ((Literal) node).positive);
		}
		// Reconstruct other nodes as well.
		else {
			final Node clone = node.clone();
			// Rewrite the child nodes.
			final Node[] oldChildNodes = node.getChildren();
			final Node[] newChildNodes = new Node[oldChildNodes.length];
			for (int iN = 0; iN < oldChildNodes.length; iN++) {
				newChildNodes[iN] = rewriteShortLabels(oldChildNodes[iN]);
			}
			clone.setChildren(newChildNodes);
			return clone;
		}
	}

	/**
	 * Sets the <i>text</i> and the <i>size</i> of the bounds of the {@link ConstraintFigure} with respect to the text and icon
	 */
	private void setText(String newText) {
		label.setText(newText);

		final Dimension labelSize = new Dimension(label.getPreferredSize());
		labelSize.expand(CONSTRAINT_INSETS.getWidth(), CONSTRAINT_INSETS.getHeight());

		label.setSize(labelSize);
		setSize(labelSize);
	}

	public Rectangle getLabelBounds() {
		return label.getBounds();
	}

	@Override
	public ModelFigure getParent() {
		return (ModelFigure) super.getParent();
	}
}
