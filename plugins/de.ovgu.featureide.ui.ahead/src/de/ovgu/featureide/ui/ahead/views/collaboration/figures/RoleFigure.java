/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.ahead.views.collaboration.figures;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.ToolbarLayout;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.core.jakprojectmodel.IField;
import de.ovgu.featureide.core.jakprojectmodel.IMethod;
import de.ovgu.featureide.ui.ahead.AheadUIPlugin;
import de.ovgu.featureide.ui.ahead.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.ahead.views.collaboration.model.Role;


/**
 * <code>RoleFigure</code> represents the graphical representation of a 
 * role in the collaboration diagram.
 * 
 * @author Constanze Adler
 */
public class RoleFigure extends Figure implements GUIDefaults{
	
	private final Label label = new Label();
	private static Image fieldPrivate = AheadUIPlugin.getImage("field_private_obj.gif");
	private static Image fieldProtected = AheadUIPlugin.getImage("field_protected_obj.gif");
	private static Image fieldPublic = AheadUIPlugin.getImage("field_public_obj.gif");
	private static Image fieldDefault = AheadUIPlugin.getImage("field_default_obj.gif");
	private static Image methodPrivate = AheadUIPlugin.getImage("private_co.gif");
	private static Image methodProtected = AheadUIPlugin.getImage("/protected_co.gif");
	private static Image methodPublic = AheadUIPlugin.getImage("public_co.gif");
	private static Image methodDefault =  AheadUIPlugin.getImage("default_co.gif");
	private static Image classImage = AheadUIPlugin.getImage("class_obj.gif");
	private static Image featureIcon = AheadUIPlugin.getImage("FeatureIconSmall.ico");
	
	public RoleFigure(Role role) {
		
		super();
		
		this.setLayoutManager(new FreeformLayout());
		
		setBorder(ROLE_BORDER);
		label.setForegroundColor(FOREGROUND);
		label.setFont(DEFAULT_FONT);
		label.setLocation(new Point(ROLE_INSETS.left, ROLE_INSETS.top));
		label.setOpaque(true);
		
		this.setName(role.getName());
		this.add(label);
		this.setOpaque(true);
		
		// next lines defines the tooltipcontent
		Figure tooltipContent = new Figure();
		ToolbarLayout contentsLayout = new ToolbarLayout();
		tooltipContent.setLayoutManager(contentsLayout);

		String name = label.getText();
		name = (name.split("[.]"))[0];
		if (role.files.size() == 0) {
			tooltipContent.add(new Label(name + " ", classImage));
			
			tooltipContent.add(new Label(role.featureName + " ", featureIcon));
			
			CompartmentFigure fieldFigure = new CompartmentFigure();
			CompartmentFigure methodFigure = new CompartmentFigure();
			
			int fieldCount = 0;
			int methodCount = 0;
			for(IField f : role.fields){
				
				Label fieldLabel = new Label(f.getFieldName() + " ");
				if (f.isPrivate()) 
					fieldLabel.setIcon(fieldPrivate);
				else if (f.isProtected())
					fieldLabel.setIcon(fieldProtected);
				else if (f.isPublic())
					fieldLabel.setIcon(fieldPublic);
				else 
					fieldLabel.setIcon(fieldDefault);
				
				if (f.isOwn(role.jakFile)) {
					fieldFigure.add(fieldLabel);
					fieldCount++;
					// TODO: show also constructors and types and returntype of methods!!!
				}
			}
			
			for(IMethod m : role.methods){
				
				Label methodLabel = new Label(m.getMethodName() + "() ");
				if (m.isPrivate())			
					methodLabel.setIcon(methodPrivate);
				else if (m.isProtected())
					methodLabel.setIcon(methodProtected);
				else if (m.isPublic())
					methodLabel.setIcon(methodPublic);
				else 
					methodLabel.setIcon(methodDefault);
			
				if (m.isOwn(role.jakFile)) {
					methodFigure.add(methodLabel);
					methodCount++;
					
				}
			}
			setName("Fields: " + fieldCount + " Methods: " + methodCount);
			
			tooltipContent.add(fieldFigure);
			tooltipContent.add(methodFigure);
		} else if (role.getName().startsWith("*.")) {
			tooltipContent.add(new Label(role.featureName + " ", featureIcon));
			CompartmentFigure fileFigure = new CompartmentFigure();
			int fileCount = 0;
			for (String file : role.files) {
				Label fieldLabel = new Label(file);
				fileFigure.add(fieldLabel);
				fileCount++;
			}
			setName("Files: "+ fileCount);
			tooltipContent.add(fileFigure);
		} else {
			tooltipContent.add(new Label(name + " ", null));
			
			tooltipContent.add(new Label(role.featureName + " ", featureIcon));
		}
		
		contentsLayout.setConstraint(this, new Rectangle(0,0,-1,-1));
		
		this.setToolTip(tooltipContent);
	}
	
	private void setName(String name) {
		
		label.setText(name);
		Dimension labelSize = label.getPreferredSize();
		
		if (labelSize.equals(label.getSize()))
			return;
		label.setSize(labelSize);

		Rectangle bounds = getBounds();
		int w = ROLE_INSETS.getWidth();
		int h = ROLE_INSETS.getHeight();
		bounds.setSize(labelSize.expand(w, h));

		Dimension oldSize = getSize();
		if (!oldSize.equals(0, 0)) {
			int dx = (oldSize.width - bounds.width) / 2;
			bounds.x += dx;
		}

		setBounds(bounds);
	}
	
}