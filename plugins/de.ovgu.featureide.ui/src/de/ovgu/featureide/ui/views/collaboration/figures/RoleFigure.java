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
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.QualifiedName;
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
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.action.ShowFieldsMethodsAction;
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

	/**
	 * This array describes the selection status of the method and field filter.
	 */
	private static boolean[] SELECTED_FIELS_METHOD = getRoleSelections();
	
	private static final QualifiedName ROLE_SELECTIONS = GET_ROLE_SELECTIONS_NAME(); 
	
	/**
	 * @return the {@link QualifiedName} of RoleSelections.
	 */
	private static QualifiedName GET_ROLE_SELECTIONS_NAME() {
		if (ROLE_SELECTIONS == null) {
			return new QualifiedName(RoleFigure.class.getName() +"#RoleSelections", 
			          				 RoleFigure.class.getName() +"#RoleSelections");
		}
		return ROLE_SELECTIONS;
	}
	
	private static final String TRUE = "true";
	private static final String FALSE = "false";
	
	public static void setSelectedFieldMethod(boolean... selections) {
		System.arraycopy(selections, 0, SELECTED_FIELS_METHOD, 0, selections.length);
		
		/*
		 * Save the status at persistent properties.
		 */
		StringBuilder builder = new StringBuilder();
		for (boolean entry : selections) {
			builder.append(entry ? TRUE : FALSE);
			builder.append('|');
		}
		
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(ROLE_SELECTIONS, builder.toString());
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	
	/**
	 * 
	 * @return The selections status of the method an field filter.
	 */
	public static boolean[] getSelectedFieldMethod() {
		return SELECTED_FIELS_METHOD.clone();
	}
	
	/**
	 * Gets the the persistent property of <i>ROLE_SELECTIONS</i>
	 * @return The persistent property
	 */
	public final static boolean[] getRoleSelections() {
		boolean[] selections = new boolean[7];
		try {
			String property = ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(GET_ROLE_SELECTIONS_NAME());
			if (property == null) {
				return selections;
			}
			int i = 0;
			for (String entry : property.split("[|]")) {
				selections[i++] = TRUE.equals(entry);
			}
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return selections;
	}

	public static class RoleFigureBorder extends AbstractBorder {
		 
		 private final int leftY;
		 private final int rightY;
		 
		 public RoleFigureBorder(int leftY, int rightY) {
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
	 
	public boolean isSelected() {
		return selected;
	}
	
	public Role getRole() {
		return role;
	}

	public RoleFigure(Role role) {
		super();
		
		this.role = role;
		selected = role.selected;
		GridLayout gridLayout = new GridLayout(1, true);
		gridLayout.verticalSpacing = GRIDLAYOUT_VERTICAL_SPACING;
		gridLayout.marginHeight = GRIDLAYOUT_MARGIN_HEIGHT;
		panel.setLayoutManager(gridLayout);
		setLayoutManager(new FreeformLayout());
		setBackgroundColor(ROLE_BACKGROUND);
	
		if (selected) {
			setBorder(COLL_BORDER_SELECTED);
		} else { 
			setBorder(COLL_BORDER_UNSELECTED);
		}
		setOpaque(true);

		if (isFieldMethodFilterActive()) {
			createContentForFieldMethodFilter();
		} else {
			createContentForDefault();
		}

		Dimension size = getSize();
		size.expand(0, gridLayout.marginHeight*2);
		setSize(size);
		add(panel);
	}

	/**
	 * TODO description
	 */
	private void createContentForDefault() {
		int fieldCount = 0;
		int methodCount = 0;
		Figure tooltipContent = new Figure();
		FlowLayout contentsLayout = new FlowLayout();
		tooltipContent.setLayoutManager(contentsLayout);
		
		if (role.files.size() == 0) {
			fieldCount = getCountForFieldContentCreate(tooltipContent);
			methodCount = getCountForMethodContentCreate(tooltipContent);
			addLabel(new Label("Fields: " + fieldCount + " Methods: "	+ methodCount));
		} else if (role.getName().startsWith("*.")) {
			setContentForFiles(new CompartmentFigure(), tooltipContent);
		} else {
			setDirectivesContent(tooltipContent, getClassName());
		}

		contentsLayout.setConstraint(this, new Rectangle(0, 0, -1, -1));
		setToolTip(tooltipContent);
	}

	/**
	 * TODO description
	 */
	private void createContentForFieldMethodFilter() {
		int fieldCount = 0;
		int methodCount = 0;
		Figure tooltipContent = new Figure();
		GridLayout contentsLayout = new GridLayout(1,true);
		tooltipContent.setLayoutManager(contentsLayout);
		
		if (role.files.size() == 0) {
			if (showOnlyFields()) {
				fieldCount = getCountForFieldContentCreate(tooltipContent);
			}
			
			if (showOnlyMethods()) {
				methodCount = getCountForMethodContentCreate(tooltipContent);
			}
			
			tooltipContent.add(new Label(" Fields: " + fieldCount + " Methods: " + methodCount + " "));

			// draw separationline between fields and methods
			if ((fieldCount > 0) && (methodCount > 0)) {
				int xyValue = fieldCount * (ROLE_PREFERED_SIZE + GRIDLAYOUT_VERTICAL_SPACING) + GRIDLAYOUT_MARGIN_HEIGHT;
				panel.setBorder(new RoleFigureBorder(xyValue, xyValue));
			}

		} else if (role.getName().startsWith("*.")) {
			setContentForFiles(tooltipContent, null);
		} else {
			setDirectivesContent(tooltipContent, getClassName());
		}
		setToolTip(tooltipContent);
	}

	/**
	 * TODO description
	 * @param tooltipContent
	 * @return
	 */
	private int getCountForMethodContentCreate(Figure tooltipContent) {
		
		CompartmentFigure methodFigure = new CompartmentFigure();
		Label label = new Label(role.featureName + " ", IMAGE_FEATURE);
		
		if (isFieldMethodFilterActive()) {
			tooltipContent.add(label);
		} else {
			methodFigure.add(label);
		}
		
		int methodCount = 0;
		for (FSTMethod m : role.methods) {
			Label methodLabel = createMethodLabel(m);

			if (m.isOwn(role.file) && matchFilter(m)) {
				methodFigure.add(methodLabel);
				methodCount++;
				
				if (isFieldMethodFilterActive()) {
					addLabel(methodLabel);
				} else {
					if (methodCount % 25 == 0) {
						tooltipContent.add(methodFigure);
						methodFigure = new CompartmentFigure();
						methodFigure.add(new Label(""));
					}
				}
			}
		}
		
		if (!isFieldMethodFilterActive()) {
			addToToolTip(methodCount, methodFigure, tooltipContent);
		}
		return methodCount;
	}
	
	private String getClassName() {
		return role.getName().split("[.]")[0];
	}

	/**
	 * TODO description
	 * @param tooltipContent
	 * @return
	 */
	private int getCountForFieldContentCreate(Figure tooltipContent) {
		CompartmentFigure fieldFigure = new CompartmentFigure();
		Label label = new Label(getClassName() + " ", IMAGE_CLASS);
		
		if (isFieldMethodFilterActive()) {
			tooltipContent.add(label);
		} else {
			fieldFigure.add(label);
		}
		
		int fieldCount = 0;
		for (FSTField f : role.fields) {
			if (f.isOwn(role.file) && matchFilter(f)) {
				Label fieldLabel = createFieldLabel(f);
				fieldFigure.add(fieldLabel);
				fieldCount++;
				
				if (isFieldMethodFilterActive()) {
					this.addLabel(fieldLabel);
				} else {
					if (fieldCount % 25 == 0) {
						tooltipContent.add(fieldFigure);
						fieldFigure = new CompartmentFigure();
						fieldFigure.add(new Label(""));
					}
				}
			}
		}
		if (!isFieldMethodFilterActive()) {
			addToToolTip(fieldCount, fieldFigure, tooltipContent);
		}
		return fieldCount;
	}
	
	
	private void addToToolTip(int elementCount, CompartmentFigure comFigure, Figure tooltipContent) {
		if (elementCount == 0) {
			comFigure.add(new Label(""));
			tooltipContent.add(comFigure);
		}
		
		if (elementCount % 25 != 0) {
			tooltipContent.add(comFigure);
		}
	}
	
	private void setContentForFiles(Figure contentContainer, Figure tooltipContent){
		featureFolder = CorePlugin.getFeatureProject(role.files.getFirst()).getSourceFolder()
				.getFolder(role.getCollaboration().getName());
		contentContainer.add(new Label(role.featureName + " ", IMAGE_FEATURE));
		int fileCount = 0;
		long size = 0;
		for (IFile file : role.files) {
			long currentSize = file.getRawLocation().toFile().length();
			size += currentSize;
			Label fieldLabel;
			final String fileName = file.getName();
			if (currentSize <= 1000000) {
				fieldLabel = new RoleFigureLabel(" " + getParentNames(file) + fileName + " (" + currentSize / 1000 + "." + currentSize % 1000 + " bytes) ", fileName);
			} else {
				fieldLabel = new RoleFigureLabel(" " + getParentNames(file) + fileName + " (" + currentSize / 1000000 + "." + currentSize / 1000 + " kb) ", fileName);
			}
			
			fileCount++;
			if (isFieldMethodFilterActive()) {
				this.addLabel(fieldLabel);
			} else {	
				contentContainer.add(fieldLabel);
				if (fileCount % 25 == 0) {
					contentContainer = new CompartmentFigure();
					contentContainer.add(new Label(""));
				}
			}
		}
		Label label; 
		if (size <= 1000000) {
			label = (new Label("Files: " + fileCount + " (" + size/ 1000 + "." + size % 1000 + " bytes) "));
		} else {
			label = (new Label("Files: " + fileCount + " (" + size/ 1000000 + "." + size / 1000 + " kb) "));
		}
		
		if (isFieldMethodFilterActive()) {
			contentContainer.add(label);
		} else {
			addLabel(label);
			if (fileCount % 25 != 0) {
				tooltipContent.add(contentContainer);
			}
		}
		

	}
	
	private void setDirectivesContent(Figure tooltipContent, String className) {
		LinkedList<String> duplicates = new LinkedList<String>();
		tooltipContent.add(new Label(className + " ", IMAGE_CLASS));
		tooltipContent.add(new Label(this.role.featureName + " ", IMAGE_FEATURE));
		this.setToolTip(tooltipContent);
		
		for (FSTDirective d : this.role.directives) {
			if (this.role.file.equals(d.file) && !duplicates.contains(d.toDependencyString())) {
				duplicates.add(d.toDependencyString());
				Label partLabel = new RoleFigureLabel(d.toDependencyString(), IMAGE_HASH, d.toDependencyString());
				addLabel(partLabel);
			}
		}
	}

	/**
	 * 
	 * @return <code>true</code> if methods and field should be displayed directly at the figure.
	 */
	public boolean isFieldMethodFilterActive() {
		return (isPublicFieldMethodFilterActive() || isDefaultFieldMethodFilterActive() || 
			   isPrivateFieldMethodFilterActive() || isProtectedFieldMethodFilterActive()) &&
			   (showOnlyFields() || showOnlyMethods());
	}
	
	
	private boolean isPublicFieldMethodFilterActive() {
		return SELECTED_FIELS_METHOD[ShowFieldsMethodsAction.PUBLIC_FIELDSMETHODS];
	}
	
	private boolean isDefaultFieldMethodFilterActive() {
		return SELECTED_FIELS_METHOD[ShowFieldsMethodsAction.DEFAULT_FIELDSMETHODS];
	}
	
	private boolean isProtectedFieldMethodFilterActive() {
		return SELECTED_FIELS_METHOD[ShowFieldsMethodsAction.PROTECTED_FIELDSMETHODS];
	}
	
	private boolean isPrivateFieldMethodFilterActive() {
		return SELECTED_FIELS_METHOD[ShowFieldsMethodsAction.PRIVATE_FIELDSMETHODS];
	}
	
	private boolean showOnlyFields() {
		return SELECTED_FIELS_METHOD[ShowFieldsMethodsAction.ONLY_FIELDS];
	}
	
	private boolean showOnlyMethods() {
		return SELECTED_FIELS_METHOD[ShowFieldsMethodsAction.ONLY_METHODS];
	}
	
	private boolean showOnlyNames() {
		return SELECTED_FIELS_METHOD[ShowFieldsMethodsAction.HIDE_PARAMETERS_AND_TYPES];
	}

	private boolean matchFilter(FSTField f) {
		return ((f.isPrivate() && isPrivateFieldMethodFilterActive()) || 
		        (f.isProtected() && isProtectedFieldMethodFilterActive()) ||
		        (f.isPublic() && isPublicFieldMethodFilterActive()) ||
		        (!f.isPrivate() && !f.isProtected() && !f.isPublic() && isDefaultFieldMethodFilterActive())||
		        (!isFieldMethodFilterActive()));
	}
	
	private boolean matchFilter(FSTMethod m) {
		return ((m.isPrivate() && isPrivateFieldMethodFilterActive()) || 
		        (m.isProtected() && isProtectedFieldMethodFilterActive()) ||
		        (m.isPublic() && isPublicFieldMethodFilterActive()) ||
		        (!m.isPrivate() && !m.isProtected() && !m.isPublic() && isDefaultFieldMethodFilterActive()) ||
		        (!isFieldMethodFilterActive()));
	}
	
	private Label createMethodLabel(FSTMethod m) {
		String name = (m.getName());
		if (showOnlyNames()){
			name = (m.getOnlyName());
		}
		Label methodLabel = new RoleFigureLabel(name, m.getName());
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
		String name = (f.getName());
		if (showOnlyNames()){
			name = (f.getOnlyName());
		}
		Label fieldLabel = new RoleFigureLabel(name, f.getName());
		if (!selected)
		fieldLabel.setForegroundColor(ROLE_FOREGROUND_UNSELECTED);
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
	
	
	private String getParentNames(IResource file) {
		IResource parent = file.getParent();
		if (parent.equals(featureFolder)) {
			return "";
		}
		return getParentNames(parent) + parent.getName() + "/";
	}

	private void addLabel(Label label) {
		if (selected) label.setForegroundColor(FOREGROUND);
		else label.setForegroundColor(ROLE_FOREGROUND_UNSELECTED);
		if (label.getFont() == null) label.setFont(DEFAULT_FONT);
		label.setLocation(new Point(ROLE_INSETS2.left, ROLE_INSETS2.top));
		label.setOpaque(true);
		
		Dimension labelSize = label.getPreferredSize();
		
		if (labelSize.equals(label.getSize()))
			return;
		label.setSize(labelSize);
		
		this.panel.add(label);
		GridLayout layout = (GridLayout) panel.getLayoutManager();

		Dimension oldSize = getSize();
		int w = labelSize.width + ROLE_INSETS.left + ROLE_INSETS.right;
		int h = labelSize.height + layout.verticalSpacing; 
		
		oldSize.expand(0, h);
		if (oldSize.width < w) oldSize.width=w;

		panel.setSize(oldSize);
		setSize(oldSize);
	}
}