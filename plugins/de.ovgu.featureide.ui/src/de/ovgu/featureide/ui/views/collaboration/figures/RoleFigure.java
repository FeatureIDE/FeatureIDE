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
package de.ovgu.featureide.ui.views.collaboration.figures;

import java.util.ArrayList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FlowLayout;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.Panel;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.model.Role;


/**
 * <code>RoleFigure</code> represents the graphical representation of a 
 * role in the collaboration diagram.
 * 
 * @author Constanze Adler
 * @author Stephan Besecke
 */
public class RoleFigure extends Figure implements GUIDefaults{

	private static Font FONT_BOLD = new Font(null,"Arial", 8, SWT.BOLD);
		
	private final Label label = new Label();
	public Boolean selected = false;
	private IFolder featureFolder;
	public Role role;
	
	public RoleFigure(Role role) {
		super();
		
		this.role = role;
		selected = role.selected;
		this.setLayoutManager(new FreeformLayout());
		
		if (selected)
			setBorder(ROLE_BORDER_SELECTED);
		else 
			setBorder(ROLE_BORDER_UNSELECTED);

		label.setForegroundColor(FOREGROUND);
		label.setFont(DEFAULT_FONT);
		label.setLocation(new Point(ROLE_INSETS.left, ROLE_INSETS.top));
		label.setOpaque(true);
		
		this.setName(role.getName());
		this.add(label);
		this.setOpaque(true);
		
		// defines the tool tip content
		Figure tooltipContent = new Figure();		
		FlowLayout contentsLayout = new FlowLayout();
		tooltipContent.setLayoutManager(contentsLayout);
		
		String name = label.getText();
		name = (name.split("[.]"))[0];
		if (role.files.size() == 0) {
			
			CompartmentFigure fieldFigure = new CompartmentFigure();
			CompartmentFigure methodFigure = new CompartmentFigure();
			
			fieldFigure.add(new Label(name + " ", IMAGE_CLASS));
			methodFigure.add(new Label(role.featureName + " ", IMAGE_FEATURE));
			
			int fieldCount = 0;
			int methodCount = 0;
			for(FSTField f : role.fields){
				
				Label fieldLabel = new Label(f.getName() + " ");
				if (f.isPrivate())
					fieldLabel.setIcon(IMAGE_FIELD_PRIVATE);
				else if (f.isProtected())
					fieldLabel.setIcon(IMAGE_FIELD_PROTECTED);
				else if (f.isPublic())
					fieldLabel.setIcon(IMAGE_FIELD_PUBLIC);
				else 
					fieldLabel.setIcon(IMAGE_FIELD_DEFAULT);
				
				if (f.isOwn(role.file)) {
					fieldFigure.add(fieldLabel);
					fieldCount++;
					if (fieldCount % 25 == 0) {
						tooltipContent.add(fieldFigure);
						fieldFigure = new CompartmentFigure();
						fieldFigure.add(new Label(""));
					}
				}
			}
			if (fieldCount == 0) {
				fieldFigure.add(new Label(""));
				tooltipContent.add(fieldFigure);
			}
			if (fieldCount % 25 != 0)
				tooltipContent.add(fieldFigure);
			
			for(FSTMethod m : role.methods){
				
				Label methodLabel = new Label(m.getName() + " ");
				if (m.refines) {
					methodLabel.setFont(FONT_BOLD);
				}
				if (m.isPrivate())			
					methodLabel.setIcon(IMAGE_METHODE_PRIVATE);
				else if (m.isProtected())
					methodLabel.setIcon(IMAGE_METHODE_PROTECTED);
				else if (m.isPublic())
					methodLabel.setIcon(IMAGE_METHODE_PUBLIC);
				else 
					methodLabel.setIcon(IMAGE_METHODE_DEFAULT);
			
				if (m.isOwn(role.file)) {
					methodFigure.add(methodLabel);
					methodCount++;
					if (methodCount % 25 == 0) {
						tooltipContent.add(methodFigure);
						methodFigure = new CompartmentFigure();
						methodFigure.add(new Label(""));
					}
				}
			}
			if (methodCount == 0) {
				methodFigure.add(new Label(""));
				tooltipContent.add(methodFigure);
			}
			if (methodCount % 25 != 0)
				tooltipContent.add(methodFigure);
			
			setName("Fields: " + fieldCount + " Methods: " + methodCount);
			
		} else if (role.getName().startsWith("*.")) {
			featureFolder = CorePlugin.getFeatureProject(role.files.getFirst())
					.getSourceFolder().getFolder(role.getCollaboration().getName());
			CompartmentFigure fileFigure = new CompartmentFigure();
			fileFigure.add(new Label(role.featureName + " ", IMAGE_FEATURE));
			int fileCount = 0;
			long size = 0;
			for (IFile file : role.files) {
				long currentSize = file.getRawLocation().toFile().length();
				size += currentSize;
				Label fieldLabel;
				if (currentSize <= 1000000) {
					fieldLabel = new Label(" " + getParentNames(file) + file.getName() + " (" + currentSize/1000 + "." + currentSize%1000 + "bytes) ");
				} else {
					fieldLabel = new Label(" " + getParentNames(file) + file.getName() + " (" + currentSize/1000000 + "." + currentSize/1000 + "kb) ");
				}
				fileFigure.add(fieldLabel);
				fileCount++;
				if (fileCount % 25 == 0) {
					tooltipContent.add(fileFigure);
					fileFigure = new CompartmentFigure();
					fileFigure.add(new Label(""));
				}
				
			}
			if (size <= 1000000) {
				setName("Files: " + fileCount + " (" + size/1000 + "." + size%1000 + "bytes) ");
			} else {
				setName("Files: " + fileCount + " (" + size/1000000 + "." + size/1000 + "kb) ");
			}
			
			if (fileCount % 25 != 0)
				tooltipContent.add(fileFigure);
		} else {
			this.setName("   ...   ");
			CompartmentFigure fileFigure = new CompartmentFigure(); 
			fileFigure.add(new Label(role.featureName + " ", IMAGE_FEATURE));
			fileFigure.add(new Label(role.getName().split("[.]")[0] + " ", IMAGE_CLASS));
			
			if(role.directives != null) {
				for(ArrayList<String> line : role.directives){
					Panel directivesPanel = new Panel();
					FlowLayout layout = new FlowLayout(true);
					layout.setMinorSpacing(0);
					layout.setMajorSpacing(0);
					directivesPanel.setLayoutManager(layout);
					boolean toBeBold = false;
					directivesPanel.add(new Label(" ", IMAGE_HASH));
					for(String part : line){
						Label partLabel = new Label(part);
						if(toBeBold)	
							partLabel.setFont(new Font(null, new FontData("Arial Unicode MS", 8, SWT.BOLD)));
						else 
							partLabel.setFont(DEFAULT_FONT);
						toBeBold = !toBeBold;
						directivesPanel.add(partLabel);
					}
					directivesPanel.add(new Label(" "));
					fileFigure.add(directivesPanel);
				}
			}
			
			tooltipContent.add(fileFigure);
		}
		
		contentsLayout.setConstraint(this, new Rectangle(0,0,-1,-1));
		
		this.setToolTip(tooltipContent);
	}
	
	/**
	 * @param file
	 * @return
	 */
	private String getParentNames(IResource file) {
		if (file.getParent().equals(featureFolder)) {
			return "";
		}
		return getParentNames(file.getParent()) + file.getParent().getName() + "/";
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