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
package de.ovgu.featureide.fm.ui.properties;

import java.util.LinkedList;

import javax.annotation.CheckReturnValue;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.draw2d.Border;
import org.eclipse.draw2d.Graphics;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIBasics;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.language.English;
import de.ovgu.featureide.fm.ui.properties.language.German;
import de.ovgu.featureide.fm.ui.properties.language.ILanguage;
import de.ovgu.featureide.fm.ui.properties.page.FMPropertyPage;

/**
 * Manages all persistent properties defined at the property page.<br> These properties are defined for the whole workspace.<br> <br>
 *
 * Use this methods instead of {@link GUIDefaults}.
 *
 * @see FMPropertyPage
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 */
@CheckReturnValue
public class FMPropertyManager extends FMPropertyManagerDefaults implements GUIDefaults {

	/*
	 * **************************************************** current values
	 ******************************************************/
	private volatile static Boolean CURRENT_HIDE_LEGEND = null;
	private volatile static Boolean CURRENT_HIDE_BORDER_COLOR = null;
	private volatile static Color CURRENT_LEGEND_FORGOUND = null;
	private volatile static Color CURRENT_LEGEND_BACKGROUND = null;
	private volatile static Color CURRENT_DECORATOR_FORGROUND_COLOR = null;
	private volatile static Color CURRENT_FEATURE_FOREGROUND = null;
	private volatile static Color CURRENT_CONCRETE_BACKGROUND = null;
	private volatile static Color CURRENT_ABSTRACT_BACKGROUND = null;
	private volatile static Color CURRENT_CONNECTION_FOREGROUND = null;
	private volatile static Color CURRENT_DIAGRAM_BACKGROUND = null;
	private volatile static Color CURRENT_LEGEND_BORDER_COLOR = null;
	private volatile static Color CURRENT_HIDDEN_FOREGROUND = null;
	private volatile static Color CURRENT_HIDDEN_BACKGROUND = null;
	private volatile static Color CURRENT_DEAD_BACKGROUND = null;
	private volatile static Color CURRENT_FEATURE_DEAD = null;
	private volatile static Color CURRENT_CONSTRAINT_BACKGROUND = null;
	private volatile static Color CURRENT_WARNING_BACKGROUND = null;
	private volatile static Color CURRENT_FEATURE_BORDER = null;
	private volatile static Color CURRENT_INHERITED_FEATURE_BORDER = null;
	private volatile static Color CURRENT_IMPORTED_FEATURE_BORDER = null;
	private volatile static Color CURRENT_INTERFACED_FEATURE_BORDER = null;
	private volatile static Color FEATURE_BORDER_SAVE = GUIBasics.createBorderColor(CONCRETE_BACKGROUND);
	private volatile static Integer CURRENT_CONSTRAINT_SPACE_Y = null;
	private volatile static Integer CURRENT_FEATURE_SPACE_Y = null;
	private volatile static Integer CURRENT_FEATURE_SPACE_X = null;
	private volatile static Integer CURRENT_LAYOUT_MARGIN_Y = null;
	private volatile static Integer CURRENT_LAYOUT_MARGIN_X = null;

	public static void reset() {
		CURRENT_HIDE_LEGEND = null;
		CURRENT_LEGEND_FORGOUND = null;
		CURRENT_LEGEND_BACKGROUND = null;
		CURRENT_DECORATOR_FORGROUND_COLOR = null;
		CURRENT_FEATURE_FOREGROUND = null;
		CURRENT_CONCRETE_BACKGROUND = null;
		CURRENT_ABSTRACT_BACKGROUND = null;
		CURRENT_CONNECTION_FOREGROUND = null;
		CURRENT_DIAGRAM_BACKGROUND = null;
		CURRENT_LEGEND_BORDER_COLOR = null;
		CURRENT_HIDDEN_FOREGROUND = null;
		CURRENT_HIDDEN_BACKGROUND = null;
		CURRENT_DEAD_BACKGROUND = null;
		CURRENT_FEATURE_DEAD = null;
		CURRENT_CONSTRAINT_BACKGROUND = null;
		CURRENT_WARNING_BACKGROUND = null;
		CURRENT_CONSTRAINT_SPACE_Y = null;
		CURRENT_FEATURE_SPACE_Y = null;
		CURRENT_FEATURE_SPACE_X = null;
		CURRENT_LAYOUT_MARGIN_Y = null;
		CURRENT_LAYOUT_MARGIN_X = null;
		CURRENT_HIDE_BORDER_COLOR = null;
		CURRENT_FEATURE_BORDER = null;
	}

	private static LinkedList<FeatureModelEditor> editors = new LinkedList<>();

	/**
	 * Register the model for property changes.
	 *
	 * @param model
	 */
	public static void registerEditor(FeatureModelEditor model) {
		editors.add(model);
	}

	/**
	 * Removes the model from listener.
	 *
	 * @param model
	 */
	public static void unregisterEditor(FeatureModelEditor model) {
		editors.remove(model);
	}

	/**
	 * Refreshes registered models.
	 */
	public static void updateEditors() {
		for (final FeatureModelEditor model : editors) {
			model.propertyChange(new FeatureIDEEvent(model, EventType.REDRAW_DIAGRAM));
		}
	}

	public static void setHideLegend(boolean value) {
		CURRENT_HIDE_LEGEND = value;
		setBoolean(QN_HIDE_LEGEND, value);
	}

	public static boolean isLegendHidden() {
		if (CURRENT_HIDE_LEGEND == null) {
			CURRENT_HIDE_LEGEND = getBoolean(QN_HIDE_LEGEND);
		}
		return CURRENT_HIDE_LEGEND;
	}

	public static void setHideBorderColor(boolean value) {
		CURRENT_HIDE_BORDER_COLOR = value;
		setBoolean(QN_HIDE_BORDER_COLOR, value);
	}

	public static boolean isBorderColorHidden() {
		if (CURRENT_HIDE_BORDER_COLOR == null) {
			CURRENT_HIDE_BORDER_COLOR = getBoolean(QN_HIDE_BORDER_COLOR);
		}
		return CURRENT_HIDE_BORDER_COLOR;
	}

	public static void setLegendForgroundColor(Color color) {
		CURRENT_LEGEND_FORGOUND = color;
		setColor(QN_LEGEND_FORGOUND, color);
	}

	public static Color getLegendForgroundColor() {
		if (CURRENT_LEGEND_FORGOUND == null) {
			CURRENT_LEGEND_FORGOUND = getColor(QN_LEGEND_FORGOUND, LEGEND_FOREGROUND);
		}
		return CURRENT_LEGEND_FORGOUND;
	}

	public static void setLegendBackgroundColor(Color color) {
		CURRENT_LEGEND_BACKGROUND = color;
		setColor(QN_LEGEND_BACKGROUND, color);
	}

	public static Color getLegendBackgroundColor() {
		if (CURRENT_LEGEND_BACKGROUND == null) {
			CURRENT_LEGEND_BACKGROUND = getColor(QN_LEGEND_BACKGROUND, LEGEND_BACKGROUND);
		}
		return CURRENT_LEGEND_BACKGROUND;
	}

	public static void setLegendBorderColor(Color color) {
		CURRENT_LEGEND_BORDER_COLOR = color;
		setColor(QN_LEGEND_BORDER, color);
	}

	public static Color getLegendBorderColor() {
		if (CURRENT_LEGEND_BORDER_COLOR == null) {
			CURRENT_LEGEND_BORDER_COLOR = getColor(QN_LEGEND_BORDER, LEGEND_BORDER_COLOR);
		}
		return CURRENT_LEGEND_BORDER_COLOR;
	}

	public static void setFeatureForgroundColor(Color color) {
		CURRENT_FEATURE_FOREGROUND = color;
		setColor(QN_FEATURE_FORGROUND, color);
	}

	public static Color getFeatureForgroundColor() {
		if (CURRENT_FEATURE_FOREGROUND == null) {
			CURRENT_FEATURE_FOREGROUND = getColor(QN_FEATURE_FORGROUND, FEATURE_FOREGROUND);
		}
		return CURRENT_FEATURE_FOREGROUND;
	}

	public static Color getDiagramBackgroundColor() {
		if (CURRENT_DIAGRAM_BACKGROUND == null) {
			CURRENT_DIAGRAM_BACKGROUND = getColor(QN_DIAGRAM_BACKGROUND, DIAGRAM_BACKGROUND);
		}
		return CURRENT_DIAGRAM_BACKGROUND;
	}

	public static void setDiagramBackgroundColor(Color color) {
		CURRENT_DIAGRAM_BACKGROUND = color;
		setColor(QN_DIAGRAM_BACKGROUND, color);
	}

	public static void setConcreteFeatureBackgroundColor(Color color) {
		CURRENT_CONCRETE_BACKGROUND = color;
		setColor(QN_FEATURE_CONCRETE, color);
	}

	public static Color getConcreteFeatureBackgroundColor() {
		if (CURRENT_CONCRETE_BACKGROUND == null) {
			CURRENT_CONCRETE_BACKGROUND = getColor(QN_FEATURE_CONCRETE, CONCRETE_BACKGROUND);
		}
		return CURRENT_CONCRETE_BACKGROUND;
	}

	public static Color getAbstractFeatureBackgroundColor() {
		if (CURRENT_ABSTRACT_BACKGROUND == null) {
			CURRENT_ABSTRACT_BACKGROUND = getColor(QN_FEATURE_ABSTRACT, ABSTRACT_BACKGROUND);
		}
		return CURRENT_ABSTRACT_BACKGROUND;
	}

	public static void setAbstractFeatureBackgroundColor(Color color) {
		CURRENT_ABSTRACT_BACKGROUND = color;
		setColor(QN_FEATURE_ABSTRACT, color);
	}

	public static Color getHiddenFeatureForgroundColor() {
		if (CURRENT_HIDDEN_FOREGROUND == null) {
			CURRENT_HIDDEN_FOREGROUND = getColor(QN_FEATURE_HIDEEN_FORGROUND, HIDDEN_FOREGROUND);
		}
		return CURRENT_HIDDEN_FOREGROUND;
	}

	public static void setHiddenFeatureForgroundColor(Color color) {
		CURRENT_HIDDEN_FOREGROUND = color;
		setColor(QN_FEATURE_HIDEEN_FORGROUND, color);
	}

	public static Color getHiddenFeatureBackgroundColor() {
		if (CURRENT_HIDDEN_BACKGROUND == null) {
			CURRENT_HIDDEN_BACKGROUND = getColor(QN_FEATURE_HIDEEN_BACKGROUND, HIDDEN_BACKGROUND);
		}
		return CURRENT_HIDDEN_BACKGROUND;
	}

	public static void setHiddenFeatureBackgroundColor(Color color) {
		CURRENT_HIDDEN_BACKGROUND = color;
		setColor(QN_FEATURE_HIDEEN_BACKGROUND, color);
	}

	public static Color getDeadFeatureBackgroundColor() {
		if (CURRENT_DEAD_BACKGROUND == null) {
			CURRENT_DEAD_BACKGROUND = getColor(QN_FEATURE_DEAD, DEAD_BACKGROUND);
		}
		return CURRENT_DEAD_BACKGROUND;
	}

	public static void setDeadFeatureBackgroundColor(Color color) {
		CURRENT_DEAD_BACKGROUND = color;
		setColor(QN_FEATURE_DEAD, color);
	}

	public static Color getFalseOptionalFeatureBackgroundColor() {
		if (CURRENT_FEATURE_DEAD == null) {
			CURRENT_FEATURE_DEAD = getColor(QN_FEATURE_DEAD, DEAD_BACKGROUND);
		}
		return CURRENT_FEATURE_DEAD;
	}

	public static void setFalseOptionalFeatureBackgroundColor(Color color) {
		CURRENT_FEATURE_DEAD = color;
		setColor(QN_FEATURE_DEAD, color);
	}

	public static Color getConstraintBackgroundColor() {
		if (CURRENT_CONSTRAINT_BACKGROUND == null) {
			CURRENT_CONSTRAINT_BACKGROUND = getColor(QN_CONSTRAINT, CONSTRAINT_BACKGROUND);
		}
		return CURRENT_CONSTRAINT_BACKGROUND;
	}

	public static Color getImplicitConstraintBackgroundColor() {
		if (CURRENT_CONSTRAINT_BACKGROUND == null) {
			CURRENT_CONSTRAINT_BACKGROUND = getColor(QN_CONSTRAINT, CONSTRAINT_BACKGROUND);
		}
		return IMPLICIT_CONSTRAINT;
	}

	Color color = new Color(null, 255, 0, 0);

	public static void setConstraintBackgroundColor(Color color) {
		CURRENT_CONSTRAINT_BACKGROUND = color;
		setColor(QN_CONSTRAINT, color);
	}

	public static void setConnectionForegroundColor(Color color) {
		CURRENT_CONNECTION_FOREGROUND = color;
		setColor(QN_CONNECTION, color);
	}

	public static Color getConnectionForegroundColor() {
		if (CURRENT_CONNECTION_FOREGROUND == null) {
			CURRENT_CONNECTION_FOREGROUND = getColor(QN_CONNECTION, CONNECTION_FOREGROUND);
		}
		return CURRENT_CONNECTION_FOREGROUND;
	}

	public static Color getWarningColor() {
		if (CURRENT_WARNING_BACKGROUND == null) {
			CURRENT_WARNING_BACKGROUND = getColor(QN_WARNING, WARNING_BACKGROUND);
		}
		return CURRENT_WARNING_BACKGROUND;
	}

	public static void setWarningColor(Color color) {
		CURRENT_WARNING_BACKGROUND = color;
		setColor(QN_WARNING, color);
	}

	public static Color getFeatureBorderColor() {
		if (CURRENT_FEATURE_BORDER == null) {
			CURRENT_FEATURE_BORDER = getColor(QN_FEATURE_BORDER, CONCRETE_BORDER_COLOR);
		}
		return CURRENT_FEATURE_BORDER;
	}

	public static void setFeatureBorderColor(Color color) {
		CURRENT_FEATURE_BORDER = color;
		setColor(QN_FEATURE_BORDER, color);
	}

	public static Color getFeatureBorderColorSave() {
		return FEATURE_BORDER_SAVE;
	}

	public static void setFeatureBorderColorSave(Color color) {
		FEATURE_BORDER_SAVE = color;
	}

	public static void setLanguage(String text) {
		setString(QN_LANGUAGE, text);
	}

	public static ILanguage getLanguage() {
		if (German.NAME.equals(getString(QN_LANGUAGE))) {
			return new German();
		}
		return new English();
	}

	public static int getLayoutMarginX() {
		if (CURRENT_LAYOUT_MARGIN_X == null) {
			CURRENT_LAYOUT_MARGIN_X = getInt(QN_LAYOUT_MARGIN_X, LAYOUT_MARGIN_X);
		}
		return CURRENT_LAYOUT_MARGIN_X;
	}

	public static void setlayoutMagrginX(int value) {
		CURRENT_LAYOUT_MARGIN_X = value;
		setInt(QN_LAYOUT_MARGIN_X, value);
	}

	public static int getLayoutMarginY() {
		if (CURRENT_LAYOUT_MARGIN_Y == null) {
			CURRENT_LAYOUT_MARGIN_Y = getInt(QN_LAYOUT_MARGIN_Y, LAYOUT_MARGIN_Y);
		}
		return CURRENT_LAYOUT_MARGIN_Y;
	}

	public static void setlayoutMagrginY(int value) {
		CURRENT_LAYOUT_MARGIN_Y = value;
		setInt(QN_LAYOUT_MARGIN_Y, value);
	}

	public static int getFeatureSpaceX() {
		if (CURRENT_FEATURE_SPACE_X == null) {
			CURRENT_FEATURE_SPACE_X = getInt(QN_FEATURE_X, FEATURE_SPACE_X);
		}
		return CURRENT_FEATURE_SPACE_X;
	}

	public static void setFeatureSpaceX(int value) {
		CURRENT_FEATURE_SPACE_X = value;
		setInt(QN_FEATURE_X, value);
	}

	public static int getFeatureSpaceY() {
		if (CURRENT_FEATURE_SPACE_Y == null) {
			CURRENT_FEATURE_SPACE_Y = getInt(QN_FEATURE_Y, FEATURE_SPACE_Y);
		}
		return CURRENT_FEATURE_SPACE_Y;
	}

	public static void setFeatureSpaceY(int value) {
		CURRENT_FEATURE_SPACE_Y = value;
		setInt(QN_FEATURE_Y, value);
	}

	public static int getConstraintSpace() {
		if (CURRENT_CONSTRAINT_SPACE_Y == null) {
			CURRENT_CONSTRAINT_SPACE_Y = getInt(QN_CONSTRAINT_SPACE, CONSTRAINT_SPACE_Y);
		}
		return CURRENT_CONSTRAINT_SPACE_Y;
	}

	public static void setConstraintSpace(int value) {
		CURRENT_CONSTRAINT_SPACE_Y = value;
		setInt(QN_CONSTRAINT_SPACE, value);
	}

	public static Color getImplicitConstraintBorderColor(boolean implicit) {
		if (implicit) {
			return GUIBasics.createBorderColor(getImplicitConstraintBackgroundColor());
		}
		return getConstraintBackgroundColor();
	}

	public static Color getConstraintBorderColor(boolean selected) {
		if (selected) {
			return GUIBasics.createBorderColor(getConstraintBackgroundColor());
		}
		return getConstraintBackgroundColor();
	}

	public static Border getConstraintBorder(boolean selected) {
		if (selected) {
			return GUIBasics.createLineBorder(getConstraintBorderColor(true), 3);
		}
		return GUIBasics.createLineBorder(getConstraintBorderColor(false), 0);
	}

	public static Border getImplicitConstraintBorder() {
		return GUIBasics.createLineBorder(getImplicitConstraintBorderColor(true), 3);
	}

	public static Border getHiddenFeatureBorder(boolean selected) {
		if (selected) {
			return GUIBasics.createLineBorder(HIDDEN_BORDER_COLOR, 3, Graphics.LINE_DOT);
		}
		return GUIBasics.createLineBorder(HIDDEN_BORDER_COLOR, 1, Graphics.LINE_DASH);
	}

	// private static Color getHiddenBorderColor() {
	// return GUIBasics.createBorderColor(getDeadFeatureBackgroundColor());
	// }

	public static Border getDeadFeatureBorder(boolean selected) {
		if (selected) {
			return GUIBasics.createLineBorder(getDeadBorderColor(), 3);
		}
		return GUIBasics.createLineBorder(getDeadBorderColor(), 1);
	}

	private static Color getDeadBorderColor() {
		return GUIBasics.createBorderColor(getDeadFeatureBackgroundColor());
	}

	public static Border getLegendBorder() {
		return GUIBasics.createLineBorder(getLegendBorderColor(), 1);
	}

	public static Border getConcreteFeatureBorder(boolean selected) {
		if (selected) {
			return GUIBasics.createLineBorder(getConcreteBorderColor(), 3);
		}
		return GUIBasics.createLineBorder(getConcreteBorderColor(), 1);
	}

	public static Border getFeatureBorder(boolean selected) {
		if (selected) {
			return GUIBasics.createLineBorder(getFeatureBorderColor(), 3);
		}
		return GUIBasics.createLineBorder(getFeatureBorderColor(), 1);
	}

	public static Border getInheritedFeatureBorder() {
		return GUIBasics.createLineBorder(getInheritedFeatureBorderColor(), 2);
	}

	public static Color getInheritedFeatureBorderColor() {
		if (CURRENT_INHERITED_FEATURE_BORDER == null) {
			CURRENT_INHERITED_FEATURE_BORDER = getColor(QN_INHERITED_FEATURE_BORDER, INHERITED_BORDER_COLOR);
		}
		return CURRENT_INHERITED_FEATURE_BORDER;
	}

	public static void setInheritedFeatureBorderColor(Color color) {
		CURRENT_INHERITED_FEATURE_BORDER = color;
		setColor(QN_INHERITED_FEATURE_BORDER, color);
	}

	public static Border getImportedFeatureBorder() {
		return GUIBasics.createLineBorder(getImportedFeatureBorderColor(), 2);
	}

	public static Color getImportedFeatureBorderColor() {
		if (CURRENT_IMPORTED_FEATURE_BORDER == null) {
			CURRENT_IMPORTED_FEATURE_BORDER = getColor(QN_IMPORTED_FEATURE_BORDER, IMPORTED_BORDER_COLOR);
		}
		return CURRENT_IMPORTED_FEATURE_BORDER;
	}

	public static void setImportedFeatureBorderColor(Color color) {
		CURRENT_IMPORTED_FEATURE_BORDER = color;
		setColor(QN_IMPORTED_FEATURE_BORDER, color);
	}

	public static Border getInterfacedFeatureBorder() {
		return GUIBasics.createLineBorder(getInterfacedFeatureBorderColor(), 2);
	}

	public static Color getInterfacedFeatureBorderColor() {
		if (CURRENT_INTERFACED_FEATURE_BORDER == null) {
			CURRENT_INTERFACED_FEATURE_BORDER = getColor(QN_INTERFACED_FEATURE_BORDER, INTERFACED_BORDER_COLOR);
		}
		return CURRENT_INTERFACED_FEATURE_BORDER;
	}

	public static void setInterfacedFeatureBorderColor(Color color) {
		CURRENT_INTERFACED_FEATURE_BORDER = color;
		setColor(QN_INTERFACED_FEATURE_BORDER, color);
	}

	private static Color getConcreteBorderColor() {
		return GUIBasics.createBorderColor(getConcreteFeatureBackgroundColor());
	}

	public static Border getAbsteactFeatureBorder(boolean selected) {
		if (selected) {
			return GUIBasics.createLineBorder(getAbstractBorderColor(), 3);
		}
		return GUIBasics.createLineBorder(getAbstractBorderColor(), 1);
	}

	private static Color getAbstractBorderColor() {
		return GUIBasics.createBorderColor(getAbstractFeatureBackgroundColor());
	}

	public static Border getHiddenLegendBorder() {
		return GUIBasics.createLineBorder(getDiagramBackgroundColor(), 1, SWT.LINE_DOT);
	}

	public static Color getDecoratorForegroundColor() {
		if (CURRENT_DECORATOR_FORGROUND_COLOR == null) {
			CURRENT_DECORATOR_FORGROUND_COLOR = getConnectionForegroundColor();
		}
		return CURRENT_DECORATOR_FORGROUND_COLOR;
	}

	public static Color getDecoratorBackgroundColor() {
		return getDiagramBackgroundColor();
	}

	public static Border getReasonBorder(Reason<?> reason) {
		return GUIBasics.createLineBorder(getReasonColor(reason), getReasonLineWidth(reason));
	}

	public static Color getReasonColor(Reason<?> reason) {
//		FMCorePlugin.getDefault().logInfo(reason.getSourceElement().getName() + " got color " + GUIBasics.createColor(reason.getConfidence(), 0.0, 0.0));
		return GUIBasics.createColor(reason.getConfidence(), 0.0, 0.0);
	}

	public static int getReasonLineWidth(Reason<?> reason) {
		return 3;
	}

	/**
	 * Gets the value(int) saved for the QualifiedName.<br> If there is no value saved, the given default value is returned.
	 *
	 * @param name The QualifiedName
	 * @param defaultValue The default value from {@link GUIDefaults}
	 * @return The value for the QualifiedName
	 */
	private static int getInt(QualifiedName name, int defaultValue) {
		try {
			final String property = workspaceRoot.getPersistentProperty(name);
			if ((property != null) && !"".equals(property)) {
				return Integer.parseInt(property);
			}
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return defaultValue;
	}

	/**
	 * Sets the value for the QualifiedName.
	 *
	 * @param name The QualifiedName
	 * @param value The value to set
	 */
	private static void setInt(QualifiedName name, int value) {
		try {
			workspaceRoot.setPersistentProperty(name, Integer.toString(value));
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Gets the value(boolean) saved for the QualifiedName.<br> If there is no value saved, it returns: <code>false</code>
	 *
	 * @param name The QualifiedName
	 * @return The value for the QualifiedName
	 */
	private static boolean getBoolean(QualifiedName name) {
		try {
			return "true".equals(workspaceRoot.getPersistentProperty(name));
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}

	/**
	 * Sets the value for the QualifiedName.
	 *
	 * @param name The QualifiedName
	 * @param value The value to set
	 */
	private static void setBoolean(QualifiedName name, boolean value) {
		try {
			workspaceRoot.setPersistentProperty(name, value ? TRUE : FALSE);
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Gets the value(Color) saved for the QualifiedName.<br> If there is no value saved, the given default value is returned.
	 *
	 * @param name The QualifiedName
	 * @param defaultColor The default value from {@link GUIDefaults}
	 * @return The value for the QualifiedName
	 */
	private static Color getColor(QualifiedName name, Color deafaultColor) {
		try {
			final String property = workspaceRoot.getPersistentProperty(name);
			if (property != null) {
				final String[] color = property.split("[|]");
				if (color.length == 3) {
					return new Color(null, Integer.parseInt(color[0]), Integer.parseInt(color[1]), Integer.parseInt(color[2]));
				}
			}
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return deafaultColor;
	}

	/**
	 * Sets the color for the QualifiedName.
	 *
	 * @param name The QualifiedName
	 * @param color The color to set
	 */
	private static void setColor(QualifiedName name, Color color) {
		final String c = color.getRed() + "|" + color.getGreen() + "|" + color.getBlue();
		try {
			workspaceRoot.setPersistentProperty(name, c);
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Gets the value(String) saved for the QualifiedName.<br> If there is no value saved, it returns: "".
	 *
	 * @param name The QualifiedName
	 * @return The value for the QualifiedName
	 */
	private static String getString(QualifiedName name) {
		try {
			if (workspaceRoot.getPersistentProperty(name) != null) {
				return workspaceRoot.getPersistentProperty(name);
			}
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return "";
	}

	/**
	 * Sets the value for the QualifiedName.
	 *
	 * @param name The QualifiedName
	 * @param value The value to set
	 */
	private static void setString(QualifiedName name, String value) {
		try {
			workspaceRoot.setPersistentProperty(name, value);
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	public static LinkedList<QualifiedName> getQualifiedNames() {
		final LinkedList<QualifiedName> names = new LinkedList<QualifiedName>();
		names.add(QN_HIDE_LEGEND);
		// names.add(QN_LEGEND_FORGOUND);
		names.add(QN_LEGEND_BACKGROUND);
		names.add(QN_LEGEND_BORDER);
		names.add(QN_LANGUAGE);
		names.add(QN_DIAGRAM_BACKGROUND);
		// names.add(QN_FEATURE_FORGROUND);
		names.add(QN_FEATURE_CONCRETE);
		names.add(QN_FEATURE_ABSTRACT);
		// names.add(QN_FEATURE_HIDEEN_FORGROUND);
		names.add(QN_FEATURE_HIDEEN_BACKGROUND);
		names.add(QN_FEATURE_DEAD);
		names.add(QN_CONSTRAINT);
		names.add(QN_CONNECTION);
		names.add(QN_WARNING);
		names.add(QN_LAYOUT_MARGIN_X);
		names.add(QN_LAYOUT_MARGIN_Y);
		names.add(QN_FEATURE_X);
		names.add(QN_FEATURE_Y);
		names.add(QN_CONSTRAINT_SPACE);
		names.add(QN_HIDE_BORDER_COLOR);
		names.add(QN_FEATURE_BORDER);
		return names;
	}

}
