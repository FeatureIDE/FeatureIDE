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
package de.ovgu.featureide.ui.views.collaboration.figures;

import static de.ovgu.featureide.fm.core.localization.StringTable.ARIAL;

import java.util.Arrays;

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
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTArbitraryRole;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.action.ShowFieldsMethodsAction;

/**
 * <code>RoleFigure</code> represents the graphical representation of a role in the collaboration diagram.
 *
 * @author Constanze Adler
 * @author Stephan Besecke
 * @author Bastian Bartens
 * @author Max Kammler
 */

public class RoleFigure extends Figure implements GUIDefaults {

	private static Font FONT_BOLD = new Font(null, ARIAL, 8, SWT.BOLD);

	private final Panel panel = new Panel();
	private boolean selected = false;

	private IFolder featureFolder;
	private final FSTRole role;

	/**
	 * This array describes the selection status of the method and field filter.
	 */
	private static boolean[] SELECTED_FIELDS_METHOD = getRoleSelections();

	private static final QualifiedName ROLE_SELECTIONS = GET_ROLE_SELECTIONS_NAME();

	/**
	 * @return the {@link QualifiedName} of RoleSelections.
	 */
	private static QualifiedName GET_ROLE_SELECTIONS_NAME() {
		if (ROLE_SELECTIONS == null) {
			return new QualifiedName(RoleFigure.class.getName() + "#RoleSelections", RoleFigure.class.getName() + "#RoleSelections");
		}
		return ROLE_SELECTIONS;
	}

	private static final String TRUE = "true";
	private static final String FALSE = "false";

	public static void setSelectedFieldMethod(boolean... selections) {
		System.arraycopy(selections, 0, SELECTED_FIELDS_METHOD, 0, selections.length);

		/*
		 * Save the status at persistent properties.
		 */
		final StringBuilder builder = new StringBuilder();
		for (final boolean entry : selections) {
			builder.append(entry ? TRUE : FALSE);
			builder.append('|');
		}

		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(ROLE_SELECTIONS, builder.toString());
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 *
	 * @return The selections status of the method an field filter.
	 */
	public static boolean[] getSelectedFieldMethod() {
		return SELECTED_FIELDS_METHOD;
	}

	/**
	 * Gets the the persistent property of <i>ROLE_SELECTIONS</i>
	 *
	 * @return The persistent property
	 */
	public final static boolean[] getRoleSelections() {
		final boolean[] selections = new boolean[14];

		// Set everything but hide_all and show_contracts as enabled (default setting)
		Arrays.fill(selections, true);
		selections[ShowFieldsMethodsAction.ONLY_CONTRACTS] = false;
		selections[ShowFieldsMethodsAction.HIDE_PARAMETERS_AND_TYPES] = false;
		selections[ShowFieldsMethodsAction.DESELECT_ALL] = false;
		selections[ShowFieldsMethodsAction.SELECT_ALL] = false;

		try {
			final String property = ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(GET_ROLE_SELECTIONS_NAME());
			if (property == null) {
				return selections;
			}
			final String[] properties = property.split("[|]");
			if (properties.length != selections.length) {
				return selections;
			}
			for (int i = 0; i < properties.length; i++) {
				selections[i] = TRUE.equals(properties[i]);

			}
		} catch (final CoreException e) {
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

		@Override
		public Insets getInsets(IFigure figure) {
			return new Insets(1, 0, 0, 0);
		}

		@Override
		public void paint(IFigure figure, Graphics graphics, Insets insets) {
			final Point left = getPaintRectangle(figure, insets).getTopLeft();
			final Point rigth = tempRect.getTopRight();
			left.y = left.y + leftY;
			rigth.y = rigth.y + rightY;
			graphics.drawLine(left, rigth);
		}
	}

	public boolean isSelected() {
		return selected;
	}

	public FSTRole getRole() {
		return role;
	}

	public RoleFigure(FSTRole role) {
		super();
		this.role = role;
		selected = role.getFeature().isSelected();
		final GridLayout gridLayout = new GridLayout(1, true);
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

		final Dimension size = getSize();
		size.expand(0, gridLayout.marginHeight * 2);
		setSize(size);

		add(panel);

	}

	private void createContentForDefault() {
		final Figure tooltipContent = new Figure();
		final FlowLayout contentsLayout = new FlowLayout();
		tooltipContent.setLayoutManager(contentsLayout);

		if (!(role instanceof FSTArbitraryRole) && role.getDirectives().isEmpty()) {
			int fieldCount = getCountForFieldContentCreate(tooltipContent);
			int methodCount = getCountForMethodContentCreate(tooltipContent);
			final Object[] invariant = createInvariantContent(tooltipContent);

			fieldCount = getCountForFields();
			methodCount = getCountForMethods();

			addLabel(new Label("Fields: " + fieldCount + " Methods: " + methodCount + " Invariants: " + (invariant[0]) + " "));
		} else if (role.getClassFragment().getName().startsWith("*.")) {
			setContentForFiles(new CompartmentFigure(), tooltipContent);

		} else {
			setDirectivesContent(tooltipContent, getClassName());
		}

		contentsLayout.setConstraint(this, new Rectangle(0, 0, -1, -1));
		setToolTip(tooltipContent);
	}

	// create content
	private void createContentForFieldMethodFilter() {
		final Figure tooltipContent = new Figure();
		final GridLayout contentsLayout = new GridLayout(1, true);
		tooltipContent.setLayoutManager(contentsLayout);

		if (role.getDirectives().isEmpty() && (role.getFile() != null)) {
			Object[] invariant = null;

			final Label label = new RoleFigureLabel(getClassName() + " ", IMAGE_CLASS, role.getClassFragment().getFullName());
			addLabel(label);

			if (showInvariants()) {
				invariant = createInvariantContent(tooltipContent);
			}

			final int fieldCount = getCountForFieldContentCreate(tooltipContent);

			int methodCount = 0;

			if (showContracts()) {
				methodCount = getCountForMethodContentContractCreate(tooltipContent);

			} else {
				methodCount = getCountForMethodContentCreate(tooltipContent);
			}

			tooltipContent.add(new Label(
					"Fields: " + fieldCount + " Methods: " + methodCount + " Invariants: " + ((invariant != null) ? ((Integer) invariant[0]) : 0) + " "));

			if (showInvariants() && (invariant != null) && (((Integer) invariant[0]) > 0)) {
				addToToolTip(((Integer) invariant[0]), ((CompartmentFigure) invariant[1]), tooltipContent);
			}

			if (shouldShowNestedClasses()) {
				createContentForInnerClasses(tooltipContent);
			}

			// TODO: Seperation lines between inner classes, fields and methods
			/*
			 * if (invariant != null && (fieldCount + ((Integer) invariant[0]) > 0) && (methodCount > 0)) { int xyValue = (fieldCount + ((Integer)
			 * invariant[0])) * (ROLE_PREFERED_SIZE + GRIDLAYOUT_VERTICAL_SPACING) + GRIDLAYOUT_MARGIN_HEIGHT; panel.setBorder(new RoleFigureBorder(xyValue,
			 * xyValue)); } else if (fieldCount > 0 && (methodCount > 0)) { int xyValue = fieldCount * (ROLE_PREFERED_SIZE + GRIDLAYOUT_VERTICAL_SPACING) +
			 * GRIDLAYOUT_MARGIN_HEIGHT; panel.setBorder(new RoleFigureBorder(xyValue, xyValue)); }
			 */

		} else if (role.getClassFragment().getName().startsWith("*.")) {
			setContentForFiles(tooltipContent, null);
		} else {
			setDirectivesContent(tooltipContent, getClassName());
		}
		setToolTip(tooltipContent);
	}

	// creates tooltip and creates content for nested classes
	private void createContentForInnerClasses(Figure tooltipContent) {

		final FSTClassFragment[] allInnerClasses = new FSTClassFragment[role.getAllInnerClasses().size()];
		role.getAllInnerClasses().toArray(allInnerClasses);

		for (final FSTClassFragment currentInnerClass : allInnerClasses) {

			// create empty label
			final Label label2 = new RoleFigureLabel("", "");
			addLabel(label2);

			// create tooltip for class
			Label label = createNestedClassLabel(currentInnerClass);
			tooltipContent.add(createNestedClassLabel(currentInnerClass));

			// create tooltip counts
			int innerFields = 0;
			int innerMethods = 0;

			addLabel(label);
			innerFields += getFieldsForInnerClass(currentInnerClass);
			innerMethods += getMethodsForInnerClass(currentInnerClass);

			label = new Label("Fields: " + innerFields + " Methods: " + innerMethods);
			tooltipContent.add(label);
		}
	}

	private int getFieldsForInnerClass(FSTClassFragment innerClassFragment) {
		int fieldCount = 0;
		for (final FSTField currentField : innerClassFragment.getFields()) {
			if (matchFilter(currentField)
				&& ((fieldsWithRefinements() && currentField.inRefinementGroup()) || (!currentField.inRefinementGroup() && fieldsWithoutRefinements()))) {
				{

					fieldCount++;
					addLabel(createFieldLabel(currentField));
				}
			}
		}
		return fieldCount;
	}

	private int getMethodsForInnerClass(FSTClassFragment innerClassFragment) {
		int methodCount = 0;

		for (final FSTMethod currentMethod : innerClassFragment.getMethods()) {
			if (matchFilter(currentMethod)
				&& ((methodsWithRefinements() && currentMethod.inRefinementGroup()) || (!currentMethod.inRefinementGroup() && methodsWithoutRefinements()))) {

				methodCount++;
				addLabel(createMethodLabel(currentMethod));
			}
		}
		return methodCount;
	}

	private int getCountForMethods() {
		return role.getClassFragment().getMethods().size();
	}

	private int getCountForFields() {
		return role.getClassFragment().getFields().size();
	}

	private int getCountForMethodContentCreate(Figure tooltipContent) {

		CompartmentFigure methodFigure = new CompartmentFigure();
		final Label label = new Label(role.getFeature() + " ", IMAGE_FEATURE);

		if (isFieldMethodFilterActive()) {
			tooltipContent.add(label);
		} else {
			methodFigure.add(label);
		}

		int methodCount = 0;

		for (final FSTMethod m : role.getClassFragment().getMethods()) {
			final Label methodLabel = createMethodLabel(m);

			// check for selected filters
			if (matchFilter(m) && ((methodsWithRefinements() && m.inRefinementGroup()) || (!m.inRefinementGroup() && methodsWithoutRefinements()))) {
				methodFigure.add(methodLabel);
				methodCount++;

				if (isFieldMethodFilterActive()) {
					addLabel(methodLabel);
				} else {
					if ((methodCount % 25) == 0) {
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

	private int getCountForMethodContentContractCreate(Figure tooltipContent) {

		CompartmentFigure methodFigure = new CompartmentFigure();
		final Label label = new Label(role.getFeature() + " ", IMAGE_FEATURE);

		if (isFieldMethodFilterActive()) {
			tooltipContent.add(label);
		} else {
			methodFigure.add(label);
		}

		int methodCount = 0;
		for (final FSTMethod m : role.getClassFragment().getMethods()) {
			final Label methodLabel = createMethodLabel(m);
			// check for selected filters
			if ((matchFilter(m) && m.hasContract())
				&& ((methodsWithRefinements() && m.inRefinementGroup()) || (!m.inRefinementGroup() && methodsWithoutRefinements()))) {
				methodFigure.add(methodLabel);
				methodCount++;

				if (isFieldMethodFilterActive()) {
					addLabel(methodLabel);
				} else {
					if ((methodCount % 25) == 0) {
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

	private Object[] createInvariantContent(Figure tooltipContent) {

		CompartmentFigure invariantFigure = new CompartmentFigure();
		invariantFigure.add(new Label(" "));
		int invariants = 0;
		for (final FSTInvariant invariant : role.getClassFragment().getInvariants()) {
			final Label invariantLabel = createInvariantLabel(invariant);

			invariantFigure.add(new Label(invariant.getBody()));
			invariants++;

			if (isFieldMethodFilterActive()) {
				addLabel(invariantLabel);
			} else {
				if ((invariants % 25) == 0) {
					tooltipContent.add(invariantFigure);
					invariantFigure = new CompartmentFigure();
					invariantFigure.add(invariantLabel);// new Label(invariant.getBody()));
				}
			}
		}

		final Object[] obj = new Object[2];
		obj[0] = invariants;
		obj[1] = invariantFigure;
		return obj;
	}

	private String getClassName() {
		String name = role.getFile().getName();
		if (name.contains("." + role.getFile().getFileExtension())) {
			name = name.substring(0, name.lastIndexOf("."));
		}
		return name;
	}

	// create label for nested class
	private Label createNestedClassLabel(FSTClassFragment classFragment) {
		String name = classFragment.getFullIdentifier();
		if (name.startsWith(RoleElement.DEFAULT_PACKAGE)) {
			name = name.substring(RoleElement.DEFAULT_PACKAGE.length());
		}
		if (name.contains(".")) {
			name = name.substring(name.lastIndexOf(".") + 1, name.length());
		}

		final RoleFigureLabel classLabel = new RoleFigureLabel(name, IMAGE_CLASS, classFragment.getFullName());
		classLabel.setForegroundColor(ROLE_FOREGROUND_UNSELECTED);
		return classLabel;
	}

	private int getCountForFieldContentCreate(Figure tooltipContent) {
		CompartmentFigure fieldFigure = new CompartmentFigure();
		final Label label = new Label(getClassName() + " ", IMAGE_CLASS);

		if (isFieldMethodFilterActive()) {
			tooltipContent.add(label);
		} else {
			fieldFigure.add(label);
		}

		int fieldCount = 0;
		for (final FSTField f : role.getClassFragment().getFields()) {
			// check for selected filters
			if (matchFilter(f) && ((fieldsWithRefinements() && f.inRefinementGroup()) || (!f.inRefinementGroup() && fieldsWithoutRefinements()))) {
				final Label fieldLabel = createFieldLabel(f);
				fieldFigure.add(fieldLabel);
				fieldCount++;

				if (isFieldMethodFilterActive()) {
					addLabel(fieldLabel);
				} else {
					if ((fieldCount % 25) == 0) {
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

		if ((elementCount % 25) != 0) {
			tooltipContent.add(comFigure);
		}
	}

	private void setContentForFiles(Figure contentContainer, Figure tooltipContent) {
		// TODO open selected file like at method and fields
		final FSTArbitraryRole role = (FSTArbitraryRole) this.role;
		final IFeatureProject project = CorePlugin.getFeatureProject(role.getFiles().get(0));
		if (project == null) {
			return;
		}
		featureFolder = project.getSourceFolder().getFolder(role.getFeature().getName());
		contentContainer.add(new Label(role.getFeature() + " ", IMAGE_FEATURE));
		int fileCount = 0;
		long size = 0;
		for (final IFile file : role.getFiles()) {
			final long currentSize = file.getRawLocation().toFile().length();
			size += currentSize;
			Label fieldLabel;
			final String fileName = file.getName();
			if (currentSize <= 1000000) {
				fieldLabel = new RoleFigureLabel(" " + getParentNames(file) + fileName + " (" + (currentSize / 1000) + "." + (currentSize % 1000) + " bytes) ",
						fileName);
			} else {
				fieldLabel = new RoleFigureLabel(" " + getParentNames(file) + fileName + " (" + (currentSize / 1000000) + "." + (currentSize / 1000) + " kb) ",
						fileName);
			}

			fileCount++;
			if (isFieldMethodFilterActive()) {
				addLabel(fieldLabel);
			} else {
				contentContainer.add(fieldLabel);
				if ((fileCount % 25) == 0) {
					contentContainer = new CompartmentFigure();
					contentContainer.add(new Label(""));
				}
			}
		}
		Label label;
		if (size <= 1000000) {
			label = (new Label("Files: " + fileCount + " (" + (size / 1000) + "." + (size % 1000) + " bytes) "));
		} else {
			label = (new Label("Files: " + fileCount + " (" + (size / 1000000) + "." + (size / 1000) + " kb) "));
		}

		if (isFieldMethodFilterActive()) {
			contentContainer.add(label);
		} else {
			addLabel(label);
			if ((fileCount % 25) != 0) {
				tooltipContent.add(contentContainer);
			}
		}

	}

	private void setDirectivesContent(Figure tooltipContent, String className) {
		tooltipContent.add(new Label(className + " ", IMAGE_CLASS));
		tooltipContent.add(new Label(role.getFeature() + " ", IMAGE_FEATURE));
		setToolTip(tooltipContent);

		for (final FSTDirective d : role.getDirectives()) {
			final String dependencyString = d.toCommandString();
			final Label partLabel = new RoleFigureLabel(dependencyString, IMAGE_HASH, dependencyString, d);
			addLabel(partLabel);
			// TODO draw separationline between fields and methods
		}
	}

	/**
	 *
	 * @return <code>true</code> if methods and field should be displayed directly at the figure.
	 */
	public boolean isFieldMethodFilterActive() {
		return (isPublicFieldMethodFilterActive() || isDefaultFieldMethodFilterActive() || isPrivateFieldMethodFilterActive()
			|| isProtectedFieldMethodFilterActive())
			&& (fieldsWithRefinements() || fieldsWithoutRefinements() || showContracts() || showInvariants() || methodsWithoutRefinements()
				|| methodsWithRefinements());
	}

	/*
	 * Get current state of selected context entrys
	 */
	private boolean methodsWithRefinements() {
		return SELECTED_FIELDS_METHOD[ShowFieldsMethodsAction.METHODS_WITH_REFINEMENTS];
	}

	private boolean shouldShowNestedClasses() {
		return SELECTED_FIELDS_METHOD[ShowFieldsMethodsAction.SHOW_NESTED_CLASSES];
	}

	private boolean methodsWithoutRefinements() {
		return SELECTED_FIELDS_METHOD[ShowFieldsMethodsAction.METHODS_WITHOUT_REFINEMENTS];
	}

	private boolean isPublicFieldMethodFilterActive() {
		return SELECTED_FIELDS_METHOD[ShowFieldsMethodsAction.PUBLIC_FIELDSMETHODS];
	}

	private boolean isDefaultFieldMethodFilterActive() {
		return SELECTED_FIELDS_METHOD[ShowFieldsMethodsAction.DEFAULT_FIELDSMETHODS];
	}

	private boolean isProtectedFieldMethodFilterActive() {
		return SELECTED_FIELDS_METHOD[ShowFieldsMethodsAction.PROTECTED_FIELDSMETHODS];
	}

	private boolean isPrivateFieldMethodFilterActive() {
		return SELECTED_FIELDS_METHOD[ShowFieldsMethodsAction.PRIVATE_FIELDSMETHODS];
	}

	private boolean fieldsWithRefinements() {
		return SELECTED_FIELDS_METHOD[ShowFieldsMethodsAction.FIELDS_WITH_REFINEMENTS];
	}

	private boolean fieldsWithoutRefinements() {
		return SELECTED_FIELDS_METHOD[ShowFieldsMethodsAction.FIELDS_WITHOUT_REFINEMENTS];
	}

	private boolean showContracts() {
		return SELECTED_FIELDS_METHOD[ShowFieldsMethodsAction.ONLY_CONTRACTS];
	}

	private boolean showInvariants() {
		return SELECTED_FIELDS_METHOD[ShowFieldsMethodsAction.ONLY_INVARIANTS];
	}

	private boolean showOnlyNames() {
		return SELECTED_FIELDS_METHOD[ShowFieldsMethodsAction.HIDE_PARAMETERS_AND_TYPES];
	}

	private boolean matchFilter(FSTField f) {
		return ((f.isPrivate() && isPrivateFieldMethodFilterActive()) || (f.isProtected() && isProtectedFieldMethodFilterActive())
			|| (f.isPublic() && isPublicFieldMethodFilterActive())
			|| (!f.isPrivate() && !f.isProtected() && !f.isPublic() && isDefaultFieldMethodFilterActive()) || (!isFieldMethodFilterActive()));
	}

	private boolean matchFilter(FSTMethod m) {
		return ((m.isPrivate() && isPrivateFieldMethodFilterActive()) || (m.isProtected() && isProtectedFieldMethodFilterActive())
			|| (m.isPublic() && isPublicFieldMethodFilterActive())
			|| (!m.isPrivate() && !m.isProtected() && !m.isPublic() && isDefaultFieldMethodFilterActive()) || (!isFieldMethodFilterActive())
			|| (m.hasContract() && showContracts()));
	}

	// create label for method
	private Label createMethodLabel(FSTMethod m) {
		String name;
		if (showOnlyNames()) {
			name = m.getName();
		} else {
			name = m.getFullName();
		}
		final Label methodLabel = new RoleFigureLabel(name, m.getFullName());

		if (m.inRefinementGroup()) {
			methodLabel.setFont(FONT_BOLD);
		}

		if (m.hasContract() && showContracts()) {
			if (m.isPrivate()) {
				methodLabel.setIcon(IMAGE_METHODE_PRIVATE_CONTRACT);
			} else if (m.isProtected()) {
				methodLabel.setIcon(IMAGE_METHODE_PROTECTED_CONTRACT);
			} else if (m.isPublic()) {
				methodLabel.setIcon(IMAGE_METHODE_PUBLIC_CONTRACT);
			} else {
				methodLabel.setIcon(IMAGE_METHODE_DEFAULT_CONTRACT);
			}
		} else {
			if (m.isPrivate()) {
				methodLabel.setIcon(IMAGE_METHODE_PRIVATE);
			} else if (m.isProtected()) {
				methodLabel.setIcon(IMAGE_METHODE_PROTECTED);
			} else if (m.isPublic()) {
				methodLabel.setIcon(IMAGE_METHODE_PUBLIC);
			} else {
				methodLabel.setIcon(IMAGE_METHODE_DEFAULT);
			}
		}

		return methodLabel;
	}

	private Label createInvariantLabel(FSTInvariant c) {

		final String fullName = c.getFullName().replace("\t", "").replace("\n", " ");

		final Label invariantLabel = new RoleFigureLabel(fullName, fullName);

		invariantLabel.setIcon(IMAGE_AT_WITHOUT_WHITE_BACKGROUND);

		return invariantLabel;
	}

	// create label for field
	private Label createFieldLabel(FSTField f) {
		String name;
		if (showOnlyNames()) {
			name = f.getName();
		} else {
			name = f.getFullName();
		}
		final Label fieldLabel = new RoleFigureLabel(name, f.getFullName());
		if (f.inRefinementGroup()) {
			fieldLabel.setFont(FONT_BOLD);
		}
		if (!selected) {
			fieldLabel.setForegroundColor(ROLE_FOREGROUND_UNSELECTED);
		}
		if (f.isPrivate()) {
			fieldLabel.setIcon(IMAGE_FIELD_PRIVATE);
		} else if (f.isProtected()) {
			fieldLabel.setIcon(IMAGE_FIELD_PROTECTED);
		} else if (f.isPublic()) {
			fieldLabel.setIcon(IMAGE_FIELD_PUBLIC);
		} else {
			fieldLabel.setIcon(IMAGE_FIELD_DEFAULT);
		}
		return fieldLabel;
	}

	private String getParentNames(IResource file) {
		final IResource parent = file.getParent();
		if (parent.equals(featureFolder)) {
			return "";
		}
		return getParentNames(parent) + parent.getName() + "/";
	}

	private void addLabel(Label label) {
		if (selected) {
			label.setForegroundColor(FOREGROUND);
		} else {
			label.setForegroundColor(ROLE_FOREGROUND_UNSELECTED);
		}
		if (label.getFont() == null) {
			label.setFont(DEFAULT_FONT);
		}
		label.setLocation(new Point(ROLE_INSETS2.left, ROLE_INSETS2.top));
		label.setOpaque(true);

		final Dimension labelSize = label.getPreferredSize();

		if (labelSize.equals(label.getSize())) {
			return;
		}
		label.setSize(labelSize);

		panel.add(label);
		final GridLayout layout = (GridLayout) panel.getLayoutManager();

		final Dimension oldSize = getSize();
		final int w = labelSize.width + ROLE_INSETS.left + ROLE_INSETS.right;
		final int h = labelSize.height + layout.verticalSpacing;

		oldSize.expand(0, h);
		if (oldSize.width < w) {
			oldSize.width = w;
		}

		panel.setSize(oldSize);
		setSize(oldSize);
	}
}
