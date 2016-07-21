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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.Panel;
import org.eclipse.draw2d.ToolbarLayout;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
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
public class ConstraintFigure extends Figure implements GUIDefaults {

	public final static String VOID_MODEL = CONSTRAINT_MAKES_THE_FEATURE_MODEL_VOID_;
	public final static String UNSATISFIABLE = CONSTRAINT_IS_UNSATISFIABLE_AND_MAKES_THE_FEATURE_MODEL_VOID_;
	public final static String TAUTOLOGY = CONSTRAINT_IS_A_TAUTOLOGY_AND_SHOULD_BE_REMOVED_;
	public final static String DEAD_FEATURE = " Constraint makes following features dead: ";
	public final static String FALSE_OPTIONAL = " Constraint makes following features false optional: ";
	public final static String REDUNDANCE = CONSTRAINT_IS_REDUNDANT_AND_COULD_BE_REMOVED_;

	private static final IFigure VOID_LABEL = new Label(VOID_MODEL);
	private static final IFigure UNSATISFIABLE_LABEL = new Label(UNSATISFIABLE);
	private static final IFigure TAUTOLOGY_LABEL = new Label(TAUTOLOGY);

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

		IConstraint constraint = this.graphicalConstraint.getObject();

		switch (constraint.getConstraintAttribute()) {
		case NORMAL:
			break;
		case VOID_MODEL:
			setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
			setToolTip(VOID_LABEL);
			break;
		case UNSATISFIABLE:
			setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
			setToolTip(UNSATISFIABLE_LABEL);
			break;
		case TAUTOLOGY:
			setBackgroundColor(FMPropertyManager.getWarningColor());
			setToolTip(TAUTOLOGY_LABEL);
			break;
		case REDUNDANT:
			setBackgroundColor(FMPropertyManager.getWarningColor());
			List<String> explanationRedundant = constraint.getFeatureModel().getAnalyser().redundantConstrExpl
					.get(FeatureUtils.getConstraintIndex(constraint.getFeatureModel(), constraint));
			Panel panelRedundant = new Panel();
			panelRedundant.setLayoutManager(new ToolbarLayout(false));
			panelRedundant.add(new Label(REDUNDANCE));
			setToolTip(panelRedundant, explanationRedundant != null ? explanationRedundant : Collections.<String> emptyList());
			return;
		case IMPLICIT:
			setBackgroundColor(FMPropertyManager.getWarningColor());
			setBorder(FMPropertyManager.getImplicitConstraintBorder());
			// set tooltip with explanation for redundant constraint
			List<String> explanationImplicit = constraint.getFeatureModel().getAnalyser().redundantConstrExpl
					.get(FeatureUtils.getConstraintIndex(constraint.getFeatureModel(), constraint));
			explanationImplicit = explanationImplicit != null ? explanationImplicit : Collections.<String> emptyList();

			// replace "redundant" with "transitive" in explanation if constraint represents an implicit dependency
			for (int i = 0; i < explanationImplicit.size(); i++) {
				if (explanationImplicit.get(i).contains("redundant")) {
					String newStr = explanationImplicit.get(i).replace("redundant", "transitive");
					explanationImplicit.set(i, newStr);
					break;
				}
			}
			Panel panelImplicit = new Panel();
			panelImplicit.setLayoutManager(new ToolbarLayout(false));
			panelImplicit.add(new Label(REDUNDANCE));
			setToolTip(panelImplicit, explanationImplicit);
			return;
		case DEAD:
		case FALSE_OPTIONAL:
			final StringBuilder toolTip = new StringBuilder();
			if (!constraint.getDeadFeatures().isEmpty()) {
				setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
				toolTip.append(DEAD_FEATURE);
				ArrayList<String> deadFeatures = new ArrayList<String>(constraint.getDeadFeatures().size());
				for (IFeature dead : constraint.getDeadFeatures()) {
					deadFeatures.add(dead.toString());
				}
				Collections.sort(deadFeatures, String.CASE_INSENSITIVE_ORDER);

				for (String dead : deadFeatures) {
					toolTip.append("\n   ");
					toolTip.append(dead);
				}
				setToolTip(new Label(toolTip.toString()));
			}

			if (!constraint.getFalseOptional().isEmpty()) {
				if (constraint.getDeadFeatures().isEmpty()) {
					setBackgroundColor(FMPropertyManager.getWarningColor());
				} else {
					toolTip.append("\n\n");
				}

				ArrayList<String> falseOptionalFeatures = new ArrayList<String>();
				for (IFeature feature : constraint.getFalseOptional()) {
					falseOptionalFeatures.add(feature.toString());
				}
				Collections.sort(falseOptionalFeatures, String.CASE_INSENSITIVE_ORDER);

				toolTip.append(FALSE_OPTIONAL);
				for (String feature : falseOptionalFeatures) {
					toolTip.append("\n   ");
					toolTip.append(feature);
				}
				setToolTip(new Label(toolTip.toString()));
			}
			break;
		default:
			break;
		}
	}

	/**
	 * Color explanation parts according to their occurrences in all explanations for a defect constraint.
	 * If expl. part occured once, it is colored black. If it occurred in every explanation, it is colored red.
	 * For all other cases, a color gradient is used.
	 * 
	 * @param panel the panel to pass for a tool tip
	 * @param expl the explanation within a tool tip
	 */
	private void setToolTip(Panel panel, List<String> expl) {
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
				panel.add(tmp);
			} else {
				Label tmp = new Label(s);
				panel.add(tmp);
			}
		}
		setToolTip(panel);
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

}
