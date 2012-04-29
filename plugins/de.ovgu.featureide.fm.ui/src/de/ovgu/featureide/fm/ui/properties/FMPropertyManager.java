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
package de.ovgu.featureide.fm.ui.properties;

import java.util.LinkedList;

import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.draw2d.Border;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIBasics;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.language.English;
import de.ovgu.featureide.fm.ui.properties.language.German;
import de.ovgu.featureide.fm.ui.properties.language.ILanguage;
import de.ovgu.featureide.fm.ui.properties.page.FMPropertyPage;

/**
 * Manages all persistent properties defined at the property pages.<br>
 * These properties are defined for the whole workspace.
 * 
 * @see FMPropertyPage
 * @author Jens Meinicke
 */
public class FMPropertyManager implements GUIDefaults {

	private static final QualifiedName QN_HIDE_LEGEND = createName("hidelegend");
	private static final QualifiedName QN_LEGEND_FORGOUND = createName("legendforground");
	private static final QualifiedName QN_LEGEND_BACKGROUND = createName("legendbackground");
	private static final QualifiedName QN_LEGEND_BORDER = createName("legendboder");

	private static final QualifiedName QN_LANGUAGE = createName("language");

	private static final QualifiedName QN_DIAGRAM_BACKGROUND = createName("diagrambackground");
	private static final QualifiedName QN_FEATURE_FORGROUND = createName("feature");
	private static final QualifiedName QN_FEATURE_CONCRETE = createName("concrete");
	private static final QualifiedName QN_FEATURE_ABSTRACT = createName("abstract");
	private static final QualifiedName QN_FEATURE_HIDEEN_FORGROUND = createName("hiddenforground");
	private static final QualifiedName QN_FEATURE_HIDEEN_BACKGROUND = createName("hiddenbackground");
	private static final QualifiedName QN_FEATURE_DEAD = createName("dead");
	private static final QualifiedName QN_CONSTRAINT = createName("constraint");
	private static final QualifiedName QN_CONNECTION = createName("connection");
	private static final QualifiedName QN_WARNING = createName("warning");

	private static final QualifiedName QN_LAYOUT_MARGIN_X = createName("margin_x");
	private static final QualifiedName QN_LAYOUT_MARGIN_Y = createName("margin_y");
	private static final QualifiedName QN_FEATURE_X = createName("feature_x");
	private static final QualifiedName QN_FEATURE_Y = createName("feature_y");
	private static final QualifiedName QN_CONSTRAINT_SPACE = createName("constraint_space");

	private static final String TRUE = "true";
	private static final String FALSE = "false";

	public static final IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();

	public static void setHideLegend(boolean value) {
		setBoolean(QN_HIDE_LEGEND, value);
	}

	public static boolean isLegendHidden() {
		return getBoolean(QN_HIDE_LEGEND);
	}

	public static void setLegendForgroundColor(Color color) {
		setColor(QN_LEGEND_FORGOUND, color);
	}

	public static Color getLegendForgroundColor() {
		return getColor(QN_LEGEND_FORGOUND, LEGEND_FOREGROUND);
	}

	public static void setLegendBackgroundColor(Color color) {
		setColor(QN_LEGEND_BACKGROUND, color);
	}

	public static Color getLegendBackgroundColor() {
		return getColor(QN_LEGEND_BACKGROUND, LEGEND_BACKGROUND);
	}

	public static void setLegendBorderColor(Color color) {
		setColor(QN_LEGEND_BORDER, color);
	}

	public static Color getLegendBorderColor() {
		return getColor(QN_LEGEND_BORDER, LEGEND_BORDER_COLOR);
	}

	public static Color getFeatureForgroundColor() {
		return getColor(QN_FEATURE_FORGROUND, FEATURE_FOREGROUND);
	}

	public static void setFeatureForgroundColor(Color color) {
		setColor(QN_FEATURE_FORGROUND, color);
	}

	public static Color getDiagramBackgroundColor() {
		return getColor(QN_DIAGRAM_BACKGROUND, DIAGRAM_BACKGROUND);
	}

	public static void setDiagramBackgroundColor(Color color) {
		setColor(QN_DIAGRAM_BACKGROUND, color);
	}

	public static Color getConcreteFeatureBackgroundColor() {
		return getColor(QN_FEATURE_CONCRETE, CONCRETE_BACKGROUND);
	}

	public static void setConcreteFeatureBackgroundColor(Color color) {
		setColor(QN_FEATURE_CONCRETE, color);
	}

	public static Color getAbstractFeatureBackgroundColor() {
		return getColor(QN_FEATURE_ABSTRACT, ABSTRACT_BACKGROUND);
	}

	public static void setAbstractFeatureBackgroundColor(Color color) {
		setColor(QN_FEATURE_ABSTRACT, color);
	}

	public static Color getHiddenFeatureForgroundColor() {
		return getColor(QN_FEATURE_HIDEEN_FORGROUND, HIDDEN_FOREGROUND);
	}

	public static void setHiddenFeatureForgroundColor(Color color) {
		setColor(QN_FEATURE_HIDEEN_FORGROUND, color);
	}

	public static Color getHiddenFeatureBackgroundColor() {
		return getColor(QN_FEATURE_HIDEEN_BACKGROUND, HIDDEN_BACKGROUND);
	}

	public static void setHiddenFeatureBackgroundColor(Color color) {
		setColor(QN_FEATURE_HIDEEN_BACKGROUND, color);
	}

	public static Color getDeadFeatureBackgroundColor() {
		return getColor(QN_FEATURE_DEAD, DEAD_BACKGROUND);
	}

	public static void setDeadFeatureBackgroundColor(Color color) {
		setColor(QN_FEATURE_DEAD, color);
	}

	public static Color getConstraintBackgroundColor() {
		return getColor(QN_CONSTRAINT, CONSTRAINT_BACKGROUND);
	}

	public static void setConstraintBackgroundColor(Color color) {
		setColor(QN_CONSTRAINT, color);
	}

	public static Color getConnectionForgroundColor() {
		return getColor(QN_CONNECTION, CONNECTION_FOREGROUND);
	}

	public static void setConnectionForgroundColor(Color color) {
		setColor(QN_CONNECTION, color);
	}

	public static Color getWarningColor() {
		return getColor(QN_WARNING, WARNING_BACKGROUND);
	}

	public static void setWarningColor(Color color) {
		setColor(QN_WARNING, color);
	}

	public static void setLanguage(String text) {
		setString(QN_LANGUAGE, text);
	}

	public static ILanguage getLanguage() {
		if (German.name.equals(getString(QN_LANGUAGE))) {
			return new German();
		}
		return new English();
	}

	public static int getLayoutMarginX() {
		return getInt(QN_LAYOUT_MARGIN_X, LAYOUT_MARGIN_X);
	}

	public static void setlayoutMagrginX(int value) {
		setInt(QN_LAYOUT_MARGIN_X, value);
	}

	public static int getLayoutMarginY() {
		return getInt(QN_LAYOUT_MARGIN_Y, LAYOUT_MARGIN_Y);
	}

	public static void setlayoutMagrginY(int value) {
		setInt(QN_LAYOUT_MARGIN_Y, value);
	}

	public static int getFeatureSpaceX() {
		return getInt(QN_FEATURE_X, FEATURE_SPACE_X);
	}

	public static void setFeatureSpaceX(int value) {
		setInt(QN_FEATURE_X, value);
	}

	public static int getFeatureSpaceY() {
		return getInt(QN_FEATURE_Y, FEATURE_SPACE_Y);
	}

	public static void setFeatureSpaceY(int value) {
		setInt(QN_FEATURE_Y, value);
	}

	public static int getConstraintSpace() {
		return getInt(QN_CONSTRAINT_SPACE, CONSTRAINT_SPACE_Y);
	}

	public static void setConstraintSpace(int value) {
		setInt(QN_CONSTRAINT_SPACE, value);
	}

	public static Color getConstrinatBorderColor(boolean selected) {
		if (selected) {
			return GUIBasics.createBorderColor(getConstraintBackgroundColor());
		}
		return getConstraintBackgroundColor();
	}

	public static Border getConstrinatBorder(boolean selected) {
		if (selected) {
			return new LineBorder(getConstrinatBorderColor(true), 3);
		}
		return new LineBorder(getConstrinatBorderColor(false), 0);
	}

	public static Border getHiddenFeatureBorder(boolean selected) {
		if (selected) {
			new LineBorder(getHiddenBorderColor(), 3, 2);
		}
		return new LineBorder(HIDDEN_BORDER_COLOR, 1, 2);
	}

	private static Color getHiddenBorderColor() {
		return GUIBasics.createBorderColor(getDeadFeatureBackgroundColor());
	}

	public static Border getDeadFeatureBorder(boolean selected) {
		if (selected) {
			return new LineBorder(getDeadBorderColor(), 3);
		}
		return new LineBorder(getDeadBorderColor(), 1);
	}

	private static Color getDeadBorderColor() {
		return GUIBasics.createBorderColor(getDeadFeatureBackgroundColor());
	}

	public static Border getLegendBorder() {
		return new LineBorder(getLegendBorderColor(), 1);
	}

	public static Border getConcreteFeatureBorder(boolean selected) {
		if (selected) {
			return new LineBorder(getConcreteBorderColor(), 3);
		}
		return new LineBorder(getConcreteBorderColor(), 1);
	}

	private static Color getConcreteBorderColor() {
		return GUIBasics.createBorderColor(getConcreteFeatureBackgroundColor());
	}

	public static Border getAbsteactFeatureBorder(boolean selected) {
		if (selected) {
			new LineBorder(getAbstractBorderColor(), 3);
		}
		return new LineBorder(getAbstractBorderColor(), 1);
	}

	private static Color getAbstractBorderColor() {
		return GUIBasics.createBorderColor(getAbstractFeatureBackgroundColor());
	}

	public static Border getHiddenLegendBorder() {
		return new LineBorder(getDiagramBackgroundColor(), 1, SWT.LINE_DOT);
	}

	public static Color getDecoratorForgroundColor() {
		return getConnectionForgroundColor();
	}

	public static Color getDecoratorBackgroundColor() {
		return getDiagramBackgroundColor();
	}

	/**
	 * Gets the value(int) saved for the QualifiedName.<br>
	 * If there is no value saved, the given default value is returned.   
	 * 
	 * @param name The QualifiedName
	 * @param defaultValue The default value from {@link GUIDefaults}
	 * @return The value for the QualifiedName
	 */
	private static int getInt(QualifiedName name, int defaultValue) {
		try {
			String property = workspaceRoot.getPersistentProperty(name);
			if (property != null && !"".equals(property)) {
				return Integer.parseInt(property);
			}
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return defaultValue;
	}

	/**
	 * Sets the value for the QualifiedName.
	 * @param name The QualifiedName
	 * @param value The value to set
	 */
	private static void setInt(QualifiedName name, int value) {
		try {
			workspaceRoot.setPersistentProperty(name, Integer.toString(value));
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Gets the value(boolean) saved for the QualifiedName.<br>
	 * If there is no value saved, it returns: <code>false</code>   
	 * 
	 * @param name The QualifiedName
	 * @return The value for the QualifiedName
	 */
	private static boolean getBoolean(QualifiedName name) {
		try {
			return "true".equals(workspaceRoot.getPersistentProperty(name));
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}

	/**
	 * Sets the value for the QualifiedName.
	 * @param name The QualifiedName
	 * @param value The value to set
	 */
	private static void setBoolean(QualifiedName name, boolean value) {
		try {
			workspaceRoot.setPersistentProperty(name, value ? TRUE : FALSE);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Gets the value(Color) saved for the QualifiedName.<br>
	 * If there is no value saved, the given default value is returned.   
	 * 
	 * @param name The QualifiedName
	 * @param defaultColor The default value from {@link GUIDefaults}
	 * @return The value for the QualifiedName
	 */
	private static Color getColor(QualifiedName name, Color deafaultColor) {
		try {
			String property = workspaceRoot.getPersistentProperty(name);
			if (property != null) {
				String[] color = property.split("[|]");
				if (color.length == 3) {
					return new Color(null, Integer.parseInt(color[0]),
							Integer.parseInt(color[1]), Integer.parseInt(color[2]));
				}
			}
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return deafaultColor;
	}

	/**
	 * Sets the color for the QualifiedName.
	 * @param name The QualifiedName
	 * @param color The color to set
	 */
	private static void setColor(QualifiedName name, Color color) {
		String c = color.getRed() + "|" + color.getGreen() + "|"
				+ color.getBlue();
		try {
			workspaceRoot.setPersistentProperty(name, c);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Gets the value(String) saved for the QualifiedName.<br>
	 * If there is no value saved, it returns: "". 
	 * 
	 * @param name The QualifiedName
	 * @return The value for the QualifiedName
	 */
	private static String getString(QualifiedName name) {
		try {
			if (workspaceRoot.getPersistentProperty(name) != null) {
				return workspaceRoot.getPersistentProperty(name);
			}
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return "";
	}

	/**
	 * Sets the value for the QualifiedName.
	 * @param name The QualifiedName
	 * @param value The value to set
	 */
	private static void setString(QualifiedName name, String value) {
		try {
			workspaceRoot.setPersistentProperty(name, value);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Creates a Qualified name.
	 * @param name the identifier for the QualifiedName
	 * @return The new QualifiedName
	 */
	private static QualifiedName createName(String name) {
		return new QualifiedName(FMCorePlugin.PLUGIN_ID + "." + name, FMCorePlugin.PLUGIN_ID + "." + name);
	}

	public static LinkedList<QualifiedName> getQualifiedNames() {
		LinkedList<QualifiedName> names = new LinkedList<QualifiedName>();
		names.add(QN_HIDE_LEGEND);
//		names.add(QN_LEGEND_FORGOUND);
		names.add(QN_LEGEND_BACKGROUND);
		names.add(QN_LEGEND_BORDER);
		names.add(QN_LANGUAGE);
		names.add(QN_DIAGRAM_BACKGROUND);
//		names.add(QN_FEATURE_FORGROUND);
		names.add(QN_FEATURE_CONCRETE);
		names.add(QN_FEATURE_ABSTRACT);
//		names.add(QN_FEATURE_HIDEEN_FORGROUND);
		names.add(QN_FEATURE_HIDEEN_BACKGROUND);
		names.add(QN_FEATURE_DEAD);
		names.add(QN_CONSTRAINT );
		names.add(QN_CONNECTION);
		names.add(QN_WARNING);
		names.add(QN_LAYOUT_MARGIN_X);
		names.add(QN_LAYOUT_MARGIN_Y);
		names.add(QN_FEATURE_X);
		names.add(QN_FEATURE_Y);
		names.add(QN_CONSTRAINT_SPACE);
		return names;
	}
}
