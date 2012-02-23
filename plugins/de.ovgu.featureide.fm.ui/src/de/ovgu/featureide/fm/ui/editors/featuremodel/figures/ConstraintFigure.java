/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.propertypage.IPersistentPropertyManager;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIBasics;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;


/**
 * A figure to view a cross-tree constraint below the feature diagram.
 * 
 * @author Thomas Thuem
 */
public class ConstraintFigure extends Figure implements GUIDefaults {
	
	private static String[] symbols = null;

	private final Label label = new Label();
	
	private Constraint constraint;

	private IPersistentPropertyManager manager;

	public final static String VOID_MODEL = " Constraint makes the feature model void. ";
	public final static String UNSATISFIABLE = " Constraint is unsatisfiable and makes the feature model void. ";
	public final static String TAUTOLOGY = " Constraint is a tautology and should be removed. ";
	public final static String DEAD_FEATURE = " Constraint makes following features dead: ";
	public final static String FALSE_OPTIONAL = " Constraint makes following features false optional: ";
	public final static String REDUNDANCE = " Constraint is redundant and could be removed. ";
	
	public ConstraintFigure(Constraint constraint) {
		super();
		this.constraint = constraint;
		manager = constraint.getFeatureModel().getPersistentPropertyManager();
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
	
	public void setConstraintProperties(boolean calc){
		setBorder(manager.getConstrinatBorder(constraint.isFeatureSelected()));
		setBackgroundColor(manager.getConstraintBackgroundColor());
		setToolTip(null);

		if(!calc)return;
		if (!constraint.getFeatureModel().valid())
			setConstraintError();
		else{
			setConstraintWarning();
		}

	}
	
	// TODO Thomas: remove this method and adopt results of analysis in constraint attributes instead
	private void setConstraintError(){
		if (constraint.getConstraintAttribute() == ConstraintAttribute.VOID_MODEL){
			setBackgroundColor(manager.getDeadFeatureBackgroundColor());
			setToolTip(new Label(VOID_MODEL));
			
		} else if (constraint.getConstraintAttribute() == ConstraintAttribute.UNSATISFIABLE) {
			setBackgroundColor(manager.getDeadFeatureBackgroundColor());
			setToolTip(new Label(UNSATISFIABLE));
		}
		
	}
	
	private void setConstraintWarning(){	
		
		if (constraint.getConstraintAttribute() == ConstraintAttribute.TAUTOLOGY){
			setBackgroundColor(manager.getDeadFeatureBackgroundColor());
			setToolTip(new Label(TAUTOLOGY));	
			return;
		}
		

		// TODO Thomas: this long calculation should be done in analyzeFeatureModel()
		if (!constraint.getDeadFeatures(constraint.getFeatureModel()).isEmpty()){
			setBackgroundColor(manager.getDeadFeatureBackgroundColor());
			StringBuilder toolTip = new StringBuilder(); 
			toolTip.append(DEAD_FEATURE);
			for (Feature dead : constraint.getDeadFeatures(constraint.getFeatureModel())) {
				toolTip.append("\n " + dead.toString());
			}
			setToolTip(new Label(toolTip.toString()));	
			return;
		}
		

		// TODO Thomas: this long calculation should be done in analyzeFeatureModel()
		if (!constraint.getFalseOptional().isEmpty()){
			setBackgroundColor(manager.getWarningColor());
			StringBuilder toolTip = new StringBuilder();
			toolTip.append(FALSE_OPTIONAL);
			for (Feature feature : constraint.getFalseOptional())
				toolTip.append("\n " + feature.getName());
			setToolTip(new Label(toolTip.toString()));	
			return;
		}
		

		if (constraint.getConstraintAttribute() == ConstraintAttribute.REDUNDANT){
			setBackgroundColor(manager.getWarningColor());
			setToolTip(new Label(REDUNDANCE));	
			return;
		}

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
