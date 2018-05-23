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
package de.ovgu.featureide.refactoring.windows;

import java.io.File;
import java.net.URI;
import java.util.EventListener;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowData;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.part.FileEditorInput;

import refactor.AstElement;
import refactor.ChangeModifier;
import refactor.ClassInfo;
import refactor.Conflict;
import refactor.FieldInfo;
import refactor.MethodInfo;
import refactor.Modified;
import refactor.ModifierInfo;
import refactor.Saveable;
import refactor.TypeSystem;
import de.ovgu.featureide.refactoring.GUIDefaults;
import de.ovgu.featureide.refactoring.typesystem.TypeSystemManager;
import de.ovgu.featureide.ui.ahead.editors.JakEditor;

/**
 * A dialog to change the modifier in a Jak file.
 * 
 * @author Stephan Kauschka
 */
public class ChangeModifierWindow implements SelectionListener, Window,
		Listener, GUIDefaults {

	private Display display;
	private Shell shell;
	private IFile file;
	private URI projectURI;
	private ITextSelection selection;
	private boolean changeInAllRefs;
	private Group group1;
	private Button cancel, change, publicMod, protectedMod, privateMod,
			noneMod, changeAll;
	private Label label1;
	private Text errorLabel;
	private Composite errorOutput;
	private ModifierInfo modifier;
	private Modified element;
	private Conflict[] conflicts;
	private Image errorImage = PlatformUI.getWorkbench().getSharedImages()
			.getImage(ISharedImages.IMG_OBJS_ERROR_TSK);

	public ChangeModifierWindow(IFile aFile, ITextSelection aSelection) {
		this.file = aFile;
		this.selection = aSelection;
		this.projectURI = this.file.getProject().getLocationURI();

		this.display = Display.getCurrent();
		if (this.display == null)
			this.display = new Display();

		this.shell = new Shell(this.display, SWT.MIN);
		this.shell.setText("Change Modifier");
		this.shell.setImage(IMAGE_SAMPLE);
		this.shell.setSize(500, 212);

		createGUI();
		this.shell.open();
	}

	public void createGUI() {
		GridLayout layout = new GridLayout();
		layout.verticalSpacing = 5;
		layout.marginHeight = 10;
		layout.marginWidth = 10;
		layout.numColumns = 1;
		layout.makeColumnsEqualWidth = false;
		this.shell.setLayout(layout);

		this.label1 = new Label(this.shell, SWT.NONE);
		String name = "";
		if (this.selection == null || this.selection.isEmpty()
				|| this.selection.getLength() == 0)
			name = this.file.getName().substring(
					0,
					this.file.getName().length()
							- this.file.getFileExtension().length() - 1);
		else
			name = selection.getText();
		this.label1.setText("Choose the new Modifier for " + name + ".");
		this.label1.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));

		this.errorOutput = new Composite(this.shell, SWT.NONE);
		this.errorOutput.setSize(this.errorOutput.getSize().x,
				2 * this.errorOutput.getSize().y);
		this.errorOutput.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		RowLayout rowLayout = new RowLayout();
		rowLayout.wrap = false;
		this.errorOutput.setLayout(rowLayout);
		Label l1 = new Label(this.errorOutput, SWT.NONE);
		l1.setImage(this.errorImage);
		this.errorLabel = new Text(this.errorOutput, SWT.WRAP | SWT.V_SCROLL);
		RowData labelData = new RowData();
		labelData.width = 446;
		labelData.height = 30;
		this.errorLabel.setLayoutData(labelData);
		this.errorLabel.setBackground(this.shell.getBackground());
		this.errorLabel.setText("line1" + "\n" + "line2");
		this.errorOutput.setVisible(false);

		group1 = new Group(this.shell, SWT.NONE);
		GridData gd = new GridData(SWT.FILL, SWT.NONE, true, false);
		gd.heightHint = 35;
		group1.setLayoutData(gd);
		RowLayout layout2 = new RowLayout();
		layout2.justify = true;
		layout2.marginHeight = 4;
		group1.setLayout(layout2);

		this.publicMod = new Button(group1, SWT.RADIO);
		this.publicMod.setText("public");
		this.publicMod.setLayoutData(new RowData());

		this.protectedMod = new Button(group1, SWT.RADIO);
		this.protectedMod.setText("protected");
		this.protectedMod.setLayoutData(new RowData());

		this.privateMod = new Button(group1, SWT.RADIO);
		this.privateMod.setText("private");
		this.privateMod.setLayoutData(new RowData());

		this.noneMod = new Button(group1, SWT.RADIO);
		this.noneMod.setText("none");
		this.noneMod.setLayoutData(new RowData());

		Group group2 = new Group(this.shell, SWT.FILL | SWT.RIGHT_TO_LEFT);
		RowLayout layout3 = new RowLayout();
		layout3.spacing = 20;
		group2.setLayout(layout3);
		group2.setLayoutData(new GridData(SWT.FILL, SWT.NONE, true, false));

		this.change = new Button(group2, SWT.NONE);
		this.change.setText("Change");
		this.change.setLayoutData(new RowData(75, 25));
		this.change.addSelectionListener(this);

		this.cancel = new Button(group2, SWT.NONE);
		this.cancel.setText("Cancel");
		this.cancel.setLayoutData(new RowData(75, 25));
		this.cancel.addSelectionListener(this);

		Composite group3 = new Composite(group2, SWT.FILL | SWT.LEFT_TO_RIGHT);
		RowLayout layout4 = new RowLayout();
		layout4.spacing = 20;
		group3.setLayout(layout4);
		group3.setLayoutData(new RowData(275, 25));

		this.changeAll = new Button(group3, SWT.CHECK);
		this.changeAll.setText("Change in all Refinements");
		this.changeAll.setLayoutData(new RowData());
		this.changeAll.setSelection(true);
		this.changeAll
				.setToolTipText("If set, the modifier is changed in the root class and all refining classes.\nOtherwise only the current class is affected.");
	}

	public void createConflictGUI() {
		this.label1
				.setText("The modifier could not be changed due to the following conflicts:");
		this.label1.pack();
		this.errorOutput.setVisible(false);

		Control[] children = this.group1.getChildren();
		for (int i = 0; i < children.length; i++) {
			if (!(children[i] instanceof EventListener))
				children[i].dispose();
		}

		GridLayout layout1 = new GridLayout();
		layout1.marginHeight = 0;
		layout1.marginWidth = 0;
		layout1.numColumns = 1;
		layout1.makeColumnsEqualWidth = false;
		this.group1.setLayout(layout1);

		Table table = new Table(this.group1, SWT.SINGLE | SWT.FULL_SELECTION
				| SWT.BORDER | SWT.V_SCROLL | SWT.H_SCROLL);
		table.addListener(SWT.MouseDoubleClick, this);
		GridData gd = new GridData(SWT.FILL, SWT.FILL, true, true);
		gd.verticalIndent = -5;
		table.setLayoutData(gd);
		table.setHeaderVisible(false);

		for (int i = 0; i < this.conflicts.length; i++) {
			TableItem item = new TableItem(table, SWT.NONE);
			item.setText(this.conflicts[i].getDescription());
		}

		this.group1.layout();
	}

	private void exit() {
		this.shell.setVisible(false);
		this.shell.dispose();
	}

	private boolean changeModifier() throws Exception {

		if (this.publicMod.getSelection() == true)
			modifier = ModifierInfo.valueOf(ModifierInfo.PUBLIC);
		else if (this.protectedMod.getSelection() == true)
			modifier = ModifierInfo.valueOf(ModifierInfo.PROTECTED);
		else if (this.privateMod.getSelection() == true)
			modifier = ModifierInfo.valueOf(ModifierInfo.PRIVATE);
		else if (this.noneMod.getSelection() == true)
			modifier = null;

		if (element == null)
			element = getModifiedElement();

		if (changeAll.getSelection() == true)
			this.changeInAllRefs = true;

		ChangeModifier cm = new ChangeModifier(element,
				new ModifierInfo[] { modifier }, this.changeInAllRefs);
		this.conflicts = cm.getConflicts();

		if (this.conflicts == null || this.conflicts.length == 0) {
			cm.changeVisibility();
			Saveable[] modified = cm.modifiedClasses();
			if (modified != null)
				for (int i = 0; i < modified.length; i++)
					modified[i].save();

			// updating the views showing the file-hierarchy requires the
			// file-system to be synchronized
			file.getProject().refreshLocal(IResource.DEPTH_INFINITE, null);
			return true;
		} else {
			createConflictGUI();
			return false;
		}
	}

	private Modified getModifiedElement() throws Exception {

		File f = new File(this.file.getLocation().toOSString());
		TypeSystem ts = TypeSystemManager.getTypesystem(projectURI);
		ClassInfo clazz = ts.getClazz(f);

		// if the file is not opened in an editor
		if (this.selection == null || this.selection.isEmpty()
				|| this.selection.getLength() == 0)
			return (Modified) clazz;

		String selectedElementName = this.selection.getText();
		int line = this.selection.getStartLine() + 1;

		FieldInfo[] fields = clazz.getFields();
		for (int i = 0; i < fields.length; i++)
			if (selectedElementName.equalsIgnoreCase(fields[i].getName()))
				if (line == ((AstElement) fields[i]).startLineNum()) {
					return (Modified) fields[i];
				}

		MethodInfo[] methods = clazz.getMethods();
		for (int i = 0; i < methods.length; i++) {
			if (selectedElementName.equalsIgnoreCase(methods[i].getName()))
				if (line == ((AstElement) methods[i]).startLineNum())
					return methods[i];
		}

		if (selectedElementName.equalsIgnoreCase(clazz.getName()))
			return (Modified) clazz;

		return null;
	}

	public void widgetSelected(SelectionEvent e) {
		if (e.getSource() == this.cancel)
			exit();

		if (e.getSource() == this.change) {

			// Wenn die �nderung schon einmal versucht wurde
			if (conflicts != null) {
				try {
					boolean successful = changeModifier();
					if (successful)
						exit();
				} catch (Exception ex) {
					setText(Window.ERROR_TEXT, ex.toString());
					return;
				}

				return;
			}

			// Wenn die �nderung zum ersten mal versucht wird
			if (this.publicMod.getSelection() == false
					&& this.protectedMod.getSelection() == false
					&& this.privateMod.getSelection() == false
					&& this.noneMod.getSelection() == false) {

				setText(Window.ERROR_TEXT, "You have to choose a new modifier.");
				return;
			}

			try {
				boolean successful = changeModifier();
				if (successful)
					exit();
			} catch (Exception ex) {
				setText(Window.ERROR_TEXT, ex.toString());
				return;
			}
		}
	}

	public void widgetDefaultSelected(SelectionEvent e) {
	}

	public void handleEvent(Event event) {

		if (event.widget instanceof Table) {
			Table source = (Table) event.widget;
			if (source.getSelectionIndex() >= 0) {
				int index = source.getSelectionIndex();
				Conflict conflict = this.conflicts[index];

				URI uri = new File(conflict.getFile()).toURI();
				IFile iFile = ResourcesPlugin.getWorkspace().getRoot()
						.findFilesForLocationURI(uri)[0];
				IFileEditorInput editorInput = new FileEditorInput(iFile);
				IWorkbenchWindow window = PlatformUI.getWorkbench()
						.getActiveWorkbenchWindow();
				IWorkbenchPage page = window.getActivePage();

				try {
					page.openEditor(editorInput, JakEditor.ID);
					TextEditor editor = ((TextEditor) page.getActiveEditor());
					IDocument document = editor.getDocumentProvider()
							.getDocument(editorInput);

					int length = 0;
					for (int i = conflict.startLine(); i <= conflict.endLine(); i++) {
						length = length + document.getLineLength(i - 1);
					}

					((TextEditor) page.getActiveEditor()).selectAndReveal(
							document.getLineOffset(conflict.startLine() - 1),
							length);
					((TextEditor) page.getActiveEditor()).selectAndReveal(
							document.getLineOffset(conflict.startLine() - 1),
							length);
				} catch (Exception e1) {
					e1.printStackTrace();
				}
			}
		}
	}

	public void setText(int component, String text) {

		if (component == Window.ERROR_TEXT) {
			this.errorLabel.setText(text);
			this.errorLabel.setToolTipText(text);
			this.errorOutput.setVisible(true);
		}

		return;
	}

	public URI getProjectURI() {
		return projectURI;
	}

}
