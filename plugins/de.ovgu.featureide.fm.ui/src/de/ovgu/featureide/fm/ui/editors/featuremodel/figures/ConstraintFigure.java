/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import java.util.ArrayList;
import java.util.Collections;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.swt.graphics.Color;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIBasics;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * A figure to view a cross-tree constraint below the feature diagram.
 * 
 * @author Thomas Thuem
 */
public class ConstraintFigure extends Figure implements GUIDefaults {
	
	private static String[] symbols = null;

	private final Label label = new Label();
	
	private Constraint constraint;

	public final static String VOID_MODEL = " Constraint makes the feature model void. ";
	public final static String UNSATISFIABLE = " Constraint is unsatisfiable and makes the feature model void. ";
	public final static String TAUTOLOGY = " Constraint is a tautology and should be removed. ";
	public final static String DEAD_FEATURE = " Constraint makes following features dead: ";
	public final static String FALSE_OPTIONAL = " Constraint makes following features false optional: ";
	public final static String REDUNDANCE = " Constraint is redundant and could be removed. ";

	private static final IFigure VOID_LABEL = new Label(VOID_MODEL);

	private static final IFigure UNSATISFIABLE_LABEL = new Label(UNSATISFIABLE);

	private static final IFigure TAUTOLOGY_LABEL = new Label(TAUTOLOGY);
	
	public ConstraintFigure(Constraint constraint) {
		super();
		this.constraint = constraint;
		setLayoutManager(new FreeformLayout());

		label.setForegroundColor(CONSTRAINT_FOREGROUND);
		label.setFont(DEFAULT_FONT);

		label.setLocation(new Point(CONSTRAINT_INSETS.left, CONSTRAINT_INSETS.top));
		
		setText(getConstraintText(constraint));		
		
		FeatureUIHelper.setSize(constraint,getSize());
		
		add(label);
		setOpaque(true);

		if (FeatureUIHelper.getLocation(constraint) != null)
			setLocation(FeatureUIHelper.getLocation(constraint));
		
		setConstraintProperties(true);
	}
	
	/**
	 * Sets the properties <i>color, border and tooltips</i> of the {@link ConstraintFigure}
	 * @param init <code>true</code> if this method is called by the constructor else the
	 * calculated properties will be set.
	 */
	public void setConstraintProperties(boolean init) {
		setBorder(FMPropertyManager.getConstraintBorder(constraint.isFeatureSelected()));
		setBackgroundColor(FMPropertyManager.getConstraintBackgroundColor());

		if(init) {
			return;
		}

		ConstraintAttribute constraintAttribute = constraint.getConstraintAttribute();
		if (constraintAttribute == ConstraintAttribute.NORMAL) {
			return;
		}
		if (constraintAttribute == ConstraintAttribute.VOID_MODEL){
			setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
			setToolTip(VOID_LABEL);
			return;
		}
		
		if (constraintAttribute == ConstraintAttribute.UNSATISFIABLE) {
			setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
			setToolTip(UNSATISFIABLE_LABEL);
			return;
		}
		
		if (constraintAttribute == ConstraintAttribute.TAUTOLOGY){
			setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
			setToolTip(TAUTOLOGY_LABEL);	
			return;
		}
		
		StringBuilder toolTip = new StringBuilder(); 
		if (!constraint.getDeadFeatures().isEmpty()){
			setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
			toolTip.append(DEAD_FEATURE);
			ArrayList<String> deadFeatures = new ArrayList<String>(constraint.getDeadFeatures().size());
			for (Feature dead : constraint.getDeadFeatures()) {
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
			
			ArrayList<String> falseOptionalFeatures = new ArrayList<String>(constraint.getFalseOptional().size());
			for (Feature feature : constraint.getFalseOptional()) {
				falseOptionalFeatures.add(feature.toString());
			}
			Collections.sort(falseOptionalFeatures, String.CASE_INSENSITIVE_ORDER);
			
			toolTip.append(FALSE_OPTIONAL);
			for (String feature : falseOptionalFeatures) {
				toolTip.append("\n   ");
				toolTip.append(feature);
			}
			setToolTip(new Label(toolTip.toString()));	
			return;
		}
		
		if (constraintAttribute == ConstraintAttribute.REDUNDANT) {
			setBackgroundColor(FMPropertyManager.getWarningColor());
			setToolTip(new Label(REDUNDANCE));	
			return;
		}

	}

	@Override
	public void setBackgroundColor(Color bg) {
		super.setBorder(new LineBorder(bg));
		super.setBackgroundColor(bg);
	}
	
	private String getConstraintText(Constraint constraint) {
		if (symbols == null) {
			symbols = NodeWriter.logicalSymbols;
			StringBuilder s = new StringBuilder();
			for (int i = 0; i < symbols.length; i++)
				s.append(symbols[i]);
			if (!GUIBasics.unicodeStringTest(label.getFont(), s.toString()))
				symbols = NodeWriter.shortSymbols;
		}
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
