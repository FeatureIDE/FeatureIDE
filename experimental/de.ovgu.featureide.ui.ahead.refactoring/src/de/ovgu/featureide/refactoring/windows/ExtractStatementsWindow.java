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
import refactor.ClassInfo;
import refactor.Conflict;
import refactor.ExtractStatements;
import refactor.LayerInfo;
import refactor.Saveable;
import refactor.TypeSystem;
import de.ovgu.featureide.refactoring.GUIDefaults;
import de.ovgu.featureide.refactoring.parser.Parser;
import de.ovgu.featureide.refactoring.typesystem.TypeSystemManager;
import de.ovgu.featureide.ui.ahead.editors.JakEditor;

/**
 * A dialog to extract statements in Jak.
 * 
 * @author Stephan Kauschka
 */
public class ExtractStatementsWindow implements Window, SelectionListener,
		Listener, GUIDefaults {

	private Display display;
	private Shell shell;
	private IFile file;
	private URI projectURI;
	private ITextSelection selection;
	private Group group1;
	private Button cancel, extract, browseLayer;
	private Label label1, label2, label3, label4;
	private Text errorLabel;
	private Composite errorOutput;
	private Text layerInput, startInput, endInput, hookInput;
	private Image folderImage = PlatformUI.getWorkbench().getSharedImages()
			.getImage(ISharedImages.IMG_OBJ_FOLDER);
	private Image errorImage = PlatformUI.getWorkbench().getSharedImages()
			.getImage(ISharedImages.IMG_OBJS_ERROR_TSK);
	private Integer start, end;
	private Conflict[] conflicts;
	private String layerInputText;
	private String hookName;
	private ExtractStatements es;

	public ExtractStatementsWindow(IFile aFile, ITextSelection aSelection) {

		this.file = aFile;
		this.selection = aSelection;

		this.projectURI = this.file.getProject().getLocationURI();

		this.display = Display.getCurrent();
		if (this.display == null)
			this.display = new Display();

		this.shell = new Shell(this.display, SWT.MIN);
		this.shell.setText("Extract Method Statements");
		this.shell.setImage(IMAGE_SAMPLE);
		this.shell.setSize(500, 250);

		if (this.selection != null) {
			this.start = this.selection.getStartLine() + 1;
			this.end = this.selection.getEndLine() + 1;
		}

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
		this.label1
				.setText("Choose the begining and end of the statement you want to extract and the destined layer.");
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

		this.group1 = new Group(this.shell, SWT.NONE);
		this.group1.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout layout2 = new GridLayout();
		layout2.verticalSpacing = 5;
		layout2.marginHeight = 10;
		layout2.marginWidth = 10;
		layout2.numColumns = 2;
		layout2.makeColumnsEqualWidth = false;
		this.group1.setLayout(layout2);

		this.label2 = new Label(group1, SWT.NONE);
		this.label2.setText("Startline: ");

		Composite rangeInput = new Composite(this.group1, SWT.NONE);
		rangeInput.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout layout3 = new GridLayout();
		layout3.verticalSpacing = 5;
		layout3.marginHeight = 0;
		layout3.marginWidth = 0;
		layout3.numColumns = 3;
		layout3.makeColumnsEqualWidth = false;
		rangeInput.setLayout(layout3);

		this.startInput = new Text(rangeInput, SWT.BORDER);
		this.startInput.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		if (this.start != null)
			this.startInput.setText(this.start + "");

		this.label3 = new Label(rangeInput, SWT.NONE);
		this.label3.setText("Endline: ");

		this.endInput = new Text(rangeInput, SWT.BORDER);
		this.endInput.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		if (this.end != null)
			this.endInput.setText(this.end + "");

		this.label4 = new Label(group1, SWT.NONE);
		this.label4.setText("DestLayer: ");

		Composite destinationInput = new Composite(this.group1, SWT.NONE);
		destinationInput.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		GridLayout layout4 = new GridLayout();
		layout4.verticalSpacing = 5;
		layout4.marginHeight = 0;
		layout4.marginWidth = 0;
		layout4.numColumns = 2;
		layout4.makeColumnsEqualWidth = false;
		destinationInput.setLayout(layout4);

		this.layerInput = new Text(destinationInput, SWT.BORDER);
		this.layerInput.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));

		this.browseLayer = new Button(destinationInput, SWT.NONE);
		this.browseLayer.setImage(this.folderImage);
		this.browseLayer.addSelectionListener(this);
		this.browseLayer.setVisible(true);

		Group group2 = new Group(this.shell, SWT.FILL | SWT.RIGHT_TO_LEFT);
		RowLayout layout5 = new RowLayout();
		layout5.spacing = 20;
		group2.setLayout(layout5);
		group2.setLayoutData(new GridData(SWT.FILL, SWT.NONE, true, false));

		this.extract = new Button(group2, SWT.NONE);
		this.extract.setText("Extract");
		this.extract.setLayoutData(new RowData(75, 25));
		this.extract.addSelectionListener(this);

		this.cancel = new Button(group2, SWT.NONE);
		this.cancel.setText("Cancel");
		this.cancel.setLayoutData(new RowData(75, 25));
		this.cancel.addSelectionListener(this);
	}

	public void createConflictGUI() {

		this.label1
				.setText("The statement could not be extracted due to the following conflicts:");
		this.label1.pack();
		this.errorOutput.setVisible(false);

		Control[] children = this.group1.getChildren();
		for (int i = 0; i < children.length; i++) {
			if (!(children[i] instanceof EventListener))
				children[i].dispose();
		}

		GridLayout layout1 = new GridLayout();
		layout1.verticalSpacing = 0;
		layout1.marginTop = 0;
		layout1.marginHeight = 0;
		layout1.marginWidth = 4;
		layout1.numColumns = 1;
		layout1.makeColumnsEqualWidth = false;
		this.group1.setLayout(layout1);

		Table table = new Table(this.group1, SWT.SINGLE | SWT.FULL_SELECTION
				| SWT.BORDER | SWT.V_SCROLL | SWT.H_SCROLL);
		table.addListener(SWT.MouseDoubleClick, this);
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		gd.heightHint = 50;
		table.setLayoutData(gd);
		table.setHeaderVisible(false);

		for (int i = 0; i < this.conflicts.length; i++) {
			TableItem item = new TableItem(table, SWT.NONE);
			item.setText(this.conflicts[i].getDescription());
		}

		this.group1.layout();
	}

	public void createHookGUI() {

		this.label1
				.setText("The extraction requires the creation of a hookmethod. Please specify a name.");
		this.label1.pack();
		this.errorOutput.setVisible(false);

		Control[] children = this.group1.getChildren();
		for (int i = 0; i < children.length; i++) {
			if (!(children[i] instanceof EventListener))
				children[i].dispose();
		}

		GridLayout layout1 = new GridLayout();
		layout1.numColumns = 2;
		layout1.makeColumnsEqualWidth = false;
		this.group1.setLayout(layout1);

		Label label = new Label(group1, SWT.NONE);
		label.setLayoutData(new GridData(SWT.CENTER, SWT.CENTER, false, false,
				1, 1));
		label.setText("Hookname: ");

		this.hookInput = new Text(group1, SWT.BORDER);
		this.hookInput.setLayoutData(new GridData(SWT.FILL, SWT.CENTER, true,
				true, 1, 1));

		this.group1.layout();
	}

	private void exit() {
		this.shell.setVisible(false);
		this.shell.dispose();
	}

	private boolean extractStatement() throws Exception {
		if (this.es == null) {
			File f = new File(this.file.getLocation().toOSString());
			TypeSystem ts = TypeSystemManager.getTypesystem(projectURI);
			ClassInfo c = ts.getClazz(f);

			// the extracted statements have to be in the scope of a method
			boolean statementsInMethod = false;
			for (int i = 0; i < c.getMethods().length; i++) {
				AstElement tmp = (AstElement) c.getMethods()[i];
				if (tmp.startLineNum() <= this.start
						&& tmp.endLineNum() >= this.end) {
					statementsInMethod = true;
					break;
				}
			}
			if (!statementsInMethod) {
				setText(Window.ERROR_TEXT,
						"The statements have to be in the scope of one method.");
				return false;
			}

			// get the source-layer and the source-class
			String srcLayer = c.getContext().getName();
			String srcClass = c.getName();

			// get the destination-layer
			String destLayer = this.layerInputText;

			LayerInfo layer = ts.getLayer(destLayer);
			String destFolder = null;
			// if the destination-layer does not exist create it
			if (layer == null) {
				destFolder = this.file.getProject().getLocation().toOSString()
						+ "\\" + Parser.FILESRC + "\\" + destLayer + "\\";
			}

			if (destFolder == null)
				this.es = new ExtractStatements(ts, srcLayer, srcClass,
						this.start, this.end, destLayer);
			else
				this.es = new ExtractStatements(ts, srcLayer, srcClass,
						this.start, this.end, destLayer, destFolder);
		}

		if (this.hookName == null && this.es.needsHook()) {
			createHookGUI();
			return false;
		}

		if (this.hookName != null && this.es.needsHook()) {
			this.es.setHookName(hookName);
		}

		this.conflicts = this.es.getConflicts();
		if (this.conflicts == null || this.conflicts.length == 0) {
			this.es.transform();
			Saveable[] modified = this.es.modifiedClasses();
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

	public void widgetSelected(SelectionEvent e) {
		if (e.getSource() == this.cancel)
			exit();

		if (e.getSource() == this.browseLayer) {
			new ChooseLayerWindow(this.shell, this);
			return;
		}

		if (e.getSource() == this.extract) {

			// Wenn die Extraktion schon einmal versucht wurde
			if (conflicts != null) {
				try {
					boolean successful = extractStatement();
					if (successful)
						exit();
				} catch (Exception ex) {
					setText(Window.ERROR_TEXT, ex.toString());
					return;
				}

				return;
			}

			// Wenn ein Hookname ben�tigt wird
			if (this.es != null && conflicts == null) {
				try {
					if (this.hookInput.getText() == null
							|| this.hookInput.getText().matches("[\\s]*")) {
						setText(Window.ERROR_TEXT,
								"You have to specify a hookname.");
						return;
					}
					this.hookName = this.hookInput.getText();
					boolean successful = extractStatement();
					if (successful)
						exit();
				} catch (Exception ex) {
					setText(Window.ERROR_TEXT, ex.toString());
					return;
				}

				return;
			}

			// Wenn die Extraktion zum ersten mal versucht wird
			try {
				if (this.startInput.getText() == null) {
					setText(Window.ERROR_TEXT,
							"You have to choose a startline.");
					return;
				}
				this.start = Integer.parseInt(this.startInput.getText());

				if (this.endInput.getText() == null) {
					setText(Window.ERROR_TEXT, "You have to choose an endline.");
					return;
				}
				this.end = Integer.parseInt(this.endInput.getText());

				if (this.layerInput.getText() == null
						|| this.layerInput.getText().matches("\\s*")) {
					setText(Window.ERROR_TEXT, "You have to choose a layer");
					return;
				}

				layerInputText = layerInput.getText();
				boolean successful = extractStatement();
				if (successful)
					exit();

			} catch (Exception ex) {
				setText(Window.ERROR_TEXT, ex.toString());
				return;
			}
		}
	}

	public void setText(int component, String text) {

		if (component == Window.ERROR_TEXT) {
			this.errorLabel.setText(text);
			this.errorLabel.setToolTipText(text);
			this.errorOutput.setVisible(true);
		}

		if (component == Window.LAYER_TEXT) {
			this.layerInput.setText(text);
		}

		return;
	}

	public URI getProjectURI() {
		return projectURI;
	}

}
