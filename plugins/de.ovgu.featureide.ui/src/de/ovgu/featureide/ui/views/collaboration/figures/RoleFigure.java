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

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.draw2d.AbstractBorder;
import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.FlowLayout;
import org.eclipse.draw2d.FreeformLayout;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.Panel;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Insets;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
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
	
	private final Panel panel = new Panel();
	private boolean selected = false;
	
	private IFolder featureFolder;
	private Role role;
	
	 public static class RoleFigureBorder extends AbstractBorder {
		 
		 private final int leftY;
		 private final int rightY;
		 
		 public RoleFigureBorder(int leftY, int rightY)
		 {
			 this.leftY = leftY;
			 this.rightY = rightY;
		 }
		 
		  public Insets getInsets(IFigure figure) {
			  return new Insets(1,0,0,0);
		  }
	    
		  public void paint(IFigure figure, Graphics graphics, Insets insets) {
			  Point left = getPaintRectangle(figure, insets).getTopLeft();
			  Point rigth = tempRect.getTopRight();
			  left.y = left.y + leftY;
			  rigth.y = rigth.y + rightY;
			  graphics.drawLine(left, rigth);
		  }
		  
	 }
	 
	public boolean isSelected() 
	{
		return selected;
	}

	
	public Role getRole() 
	{
		return role;
	}

	public RoleFigure(Role role) {
		super();
		
		this.role = role;
		selected = role.selected;
		GridLayout gridLayout = new GridLayout(1, true);
		gridLayout.verticalSpacing = ROLE_GRIDLAYOUT_VERTICAL_SPACING;
		gridLayout.marginHeight = ROLE_GRIDLAYOUT_MARGIN_HEIGHT;
		panel.setLayoutManager(gridLayout);
		this.setLayoutManager(new FreeformLayout());
		this.setSize(0, gridLayout.marginHeight*2);
	
		if (selected)
			setBorder(ROLE_BORDER_SELECTED);
		else 
			setBorder(ROLE_BORDER_UNSELECTED);
		
		this.add(panel);
		
		this.setOpaque(true);
		
		// defines the tool tip content
		Figure tooltipContent = new Figure();		
		FlowLayout contentsLayout = new FlowLayout();
		tooltipContent.setLayoutManager(contentsLayout);
		
		int fieldCount = 0;
		int methodCount = 0;
		
		if (this.role.showCompleteOutline) {

			if (role.files.size() == 0) {

				for (FSTField f : role.fields) {
					if (f.isOwn(role.file)) {
						Label fieldLabel = createFieldLabel(f);
						this.addLabel(fieldLabel);
						fieldCount++;
					}
				}

				for (FSTMethod m : role.methods) {

					if (m.isOwn(role.file)) {
						Label methodLabel = createMethodLabel(m);
						this.addLabel(methodLabel);
						methodCount++;
					}
				}

				tooltipContent.add(new Label(" Fields: " + fieldCount
						+ " Methods: " + methodCount + " "));
				this.setToolTip(tooltipContent);

				// draw separationline between fields and methods
				if ((fieldCount > 0) && (methodCount > 0)) {
					int xyValue = fieldCount * (ROLE_PREFERED_SIZE + ROLE_GRIDLAYOUT_VERTICAL_SPACING) + ROLE_GRIDLAYOUT_MARGIN_HEIGHT;
					panel.setBorder(new RoleFigureBorder(xyValue, xyValue));
				}

			} else if (role.getName().startsWith("*.")) {
				featureFolder = CorePlugin.getFeatureProject(role.files.getFirst()).getSourceFolder()
						.getFolder(role.getCollaboration().getName());
				int fileCount = 0;
				long size = 0;
				for (IFile file : role.files) {
					long currentSize = file.getRawLocation().toFile().length();
					size += currentSize;
					Label fieldLabel;
					if (currentSize <= 1000000) {
						fieldLabel = new Label(" " + getParentNames(file) + file.getName() + " (" + currentSize / 1000 + "." + currentSize % 1000 + " bytes) ");
					} 
					else {
						fieldLabel = new Label(" " + getParentNames(file) + file.getName() + " (" + currentSize / 1000000 + "." + currentSize / 1000 + " kb) ");
					}
					this.addLabel(fieldLabel);

					fileCount++;
				}
				if (size <= 1000000) {
					tooltipContent.add(new Label(" Files: " + fileCount + " (" + size / 1000 + "." + size % 1000 + " bytes) "));
				} 
				else {
					tooltipContent.add(new Label(" Files: " + fileCount + " (" + size / 1000000 + "." + size / 1000 + " kb) "));
				}
				this.setToolTip(tooltipContent);
			} 
			else {
				LinkedList<String> duplicates = new LinkedList<String>();
				for (FSTDirective d : role.directives) {
					if (role.file.equals(d.file) && !duplicates.contains(d.toDependencyString())) {
						duplicates.add(d.toDependencyString());
						Label partLabel = new Label(d.toDependencyString(),	IMAGE_HASH);
						this.addLabel(partLabel);
					}
				}
			}
		} else {
			String name = role.getName();
			name = (name.split("[.]"))[0];
			if (role.files.size() == 0) {

				CompartmentFigure fieldFigure = new CompartmentFigure();
				CompartmentFigure methodFigure = new CompartmentFigure();

				fieldFigure.add(new Label(name + " ", IMAGE_CLASS));
				methodFigure.add(new Label(role.featureName + " ",
						IMAGE_FEATURE));

				for (FSTField f : role.fields) {

					if (f.isOwn(role.file)) {
						Label fieldLabel = createFieldLabel(f);
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

				for (FSTMethod m : role.methods) {
					Label methodLabel = createMethodLabel(m);

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

				this.addLabel(new Label("Fields: " + fieldCount + " Methods: "	+ methodCount));

			} else if (role.getName().startsWith("*.")) {
				featureFolder = CorePlugin.getFeatureProject(role.files.getFirst()).getSourceFolder()
						.getFolder(role.getCollaboration().getName());
				CompartmentFigure fileFigure = new CompartmentFigure();
				fileFigure.add(new Label(role.featureName + " ", IMAGE_FEATURE));
				int fileCount = 0;
				long size = 0;
				for (IFile file : role.files) {
					long currentSize = file.getRawLocation().toFile().length();
					size += currentSize;
					Label fieldLabel;
					if (currentSize <= 1000000) {
						fieldLabel = new Label(" " + getParentNames(file) + file.getName() + " (" + currentSize / 1000 + "." + currentSize % 1000 + " bytes) ");
					} else {
						fieldLabel = new Label(" " + getParentNames(file) + file.getName() + " (" + currentSize / 1000000 + "." + currentSize / 1000 + " kb) ");
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
					this.addLabel(new Label("Files: " + fileCount + " (" + size/ 1000 + "." + size % 1000 + " bytes) "));
				} else {
					this.addLabel(new Label("Files: " + fileCount + " (" + size/ 1000000 + "." + size / 1000 + " kb) "));
				}

				if (fileCount % 25 != 0)
					tooltipContent.add(fileFigure);
			} else {
				this.addLabel(new Label("   ...   "));
				CompartmentFigure fileFigure = new CompartmentFigure();
				fileFigure.add(new Label(role.featureName + " ", IMAGE_FEATURE));
				fileFigure.add(new Label(role.getName().split("[.]")[0] + " ", IMAGE_CLASS));
				LinkedList<String> duplicates = new LinkedList<String>();

				for (FSTDirective d : role.directives) {
					if (role.file.equals(d.file) && !duplicates.contains(d.toDependencyString())) {
						duplicates.add(d.toDependencyString());
						Panel directivesPanel = new Panel();
						FlowLayout layout = new FlowLayout(true);
						layout.setMinorSpacing(0);
						layout.setMajorSpacing(0);
						directivesPanel.setLayoutManager(layout);
						Label partLabel = new Label(d.toDependencyString(), IMAGE_HASH);
						partLabel.setFont(DEFAULT_FONT);
						directivesPanel.add(partLabel);

						directivesPanel.add(new Label(" "));
						fileFigure.add(directivesPanel);
					}
				}

				tooltipContent.add(fileFigure);
			}

			contentsLayout.setConstraint(this, new Rectangle(0, 0, -1, -1));

			this.setToolTip(tooltipContent);
		}
	}


	/**
	 * @param m
	 * @return
	 */
	private Label createMethodLabel(FSTMethod m) {
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
		return methodLabel;
	}


	/**
	 * @param f
	 * @return
	 */
	private Label createFieldLabel(FSTField f) {
		Label fieldLabel = new Label(f.getName() + " ");
		if (f.isPrivate())
			fieldLabel.setIcon(IMAGE_FIELD_PRIVATE);
		else if (f.isProtected())
			fieldLabel.setIcon(IMAGE_FIELD_PROTECTED);
		else if (f.isPublic())
			fieldLabel.setIcon(IMAGE_FIELD_PUBLIC);
		else
			fieldLabel.setIcon(IMAGE_FIELD_DEFAULT);
		return fieldLabel;
	}
	
	/**
	 * @param file
	 * @return
	 */
	private String getParentNames(IResource file) {
		IResource parent = file.getParent();
		if (parent.equals(featureFolder)) {
			return "";
		}
		return getParentNames(parent) + parent.getName() + "/";
	}

	private void addLabel(Label label) {
		
		label.setForegroundColor(FOREGROUND);
		if (label.getFont() == null) label.setFont(DEFAULT_FONT);
		label.setLocation(new Point(ROLE_INSETS2.left, ROLE_INSETS2.top));
		label.setOpaque(true);
		
		Dimension labelSize = label.getPreferredSize();
		
		if (labelSize.equals(label.getSize()))
			return;
		label.setSize(labelSize);
		
		panel.add(label);
		GridLayout layout = (GridLayout) panel.getLayoutManager();

		Dimension oldSize = getSize();
		int w = labelSize.width + ROLE_INSETS.left + ROLE_INSETS.right;
		int h = labelSize.height + layout.verticalSpacing; 
		
		oldSize.expand(0, h);
		if (oldSize.width() < w) oldSize.setWidth(w);

		panel.setSize(oldSize);
		setSize(oldSize);
	}
}