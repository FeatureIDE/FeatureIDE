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
package de.ovgu.featureide.fm.ui.editors;

import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.CellLabelProvider;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerCell;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.layout.FormLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.program.Program;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;
import org.prop4j.Node;
import org.prop4j.NodeWriter;
import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.guidsl.FeatureModelReader;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * A simple editor for propositional constraints written below the feature
 * diagram.
 * 
 * @author Christian Becker
 * @author Thomas Thuem
 * @author David Broneske
 * @author Fabian Benduhn
 */
public class ConstraintDialog {

	private static final Image HELP_IMAGE = FMUIPlugin.getImage("help.gif");
	private static final Image ERROR_IMAGE = FMUIPlugin
			.getImage("icon_error.gif");
	private static final Image BANNER_IMAGE = FMUIPlugin
			.getImage("title_banner.gif");

	// TODO: AtMost1 implementieren!!

	private static final String[] OPERATOR_NAMES = { "Not", "And", "Or",
			"Implies", "Iff", "(", ")" /* "At most 1" */};
	private static final String FILTERTEXT = "type filter text";
	private Shell shell;

	private GridData gridData;
	private String initialConstraint;

	private Composite headComposite;
	private Image errorImage;
	private Label imageLabel;
	private Label errorMarker;
	private Label errorMessage;
	private String titleText;
	private String headerText;
	private Group featureGroup;
	private StyledText searchFeatureText;
	private Table featureTable;

	private Group buttonGroup;

	private Text constraintText;
	private Composite lastComposite;

	private ToolBar helpButtonBar;
	private ToolItem helpButton;

	private Button cancelButton;
	private int x, y;
	private Button okButton;

	/**
	 * 
	 * @param featuremodel
	 * @param constraint
	 */
	public ConstraintDialog(final FeatureModel featuremodel,
			final Constraint constraint) {

		if (constraint == null) {
			titleText = "Create Propositional Constraint";
			headerText = "Create new Constraint";
			initialConstraint = "";

		} else {
			titleText = "Edit Propositional Constraint";
			headerText = "Edit your Constraint";
			initialConstraint = constraint.getNode().toString(
					NodeWriter.textualSymbols);
		}
	
		initShell();
		initHead();
		initFeatureGroup(featuremodel);
		initButtonGroup();
		initConstraintText();
		initBottom(featuremodel, constraint);
		constraintText.setFocus();
		constraintText.setSelection(constraintText.getCharCount());
		shell.open();
	}

	/**
	 * 
	 */
	private void initShell() {
		shell = new Shell(Display.getCurrent());
		shell.setText(titleText);
		shell.setSize(500, 500);
		GridLayout shellLayout = new GridLayout();
		shellLayout.marginWidth = 0;
		shellLayout.marginHeight = 0;
		shell.setLayout(shellLayout);
	}

	/**
	 * @param featuremodel
	 * @param constraint
	 */
	private void initBottom(final FeatureModel featuremodel,
			final Constraint constraint) {
		gridData = new GridData(GridData.FILL_HORIZONTAL);

		lastComposite = new Composite(shell, SWT.NONE);
		lastComposite.setLayoutData(gridData);

		FormLayout lastCompositeLayout = new FormLayout();
		lastCompositeLayout.marginHeight = 5;
		lastCompositeLayout.marginWidth = 5;
		lastComposite.setLayout(lastCompositeLayout);
		helpButtonBar = new ToolBar(lastComposite, SWT.FLAT);
		helpButton = new ToolItem(helpButtonBar, SWT.NONE);
		helpButton.setImage(HELP_IMAGE);
		helpButton
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {
						Program.launch("http://www.cs.utexas.edu/~schwartz/ATS/fopdocs/guidsl.html");
					}
				});
		FormData formDataHelp = new FormData();
		formDataHelp.left = new FormAttachment(0, 5);
		helpButtonBar.setLayoutData(formDataHelp);

		cancelButton = new Button(lastComposite, SWT.NONE);
		cancelButton.setText("Cancel");
		FormData formDataCancel = new FormData();
		formDataCancel.width = 70;
		formDataCancel.right = new FormAttachment(100, -5);
		formDataCancel.bottom = new FormAttachment(100, -5);
		cancelButton.setLayoutData(formDataCancel);

		okButton = new Button(lastComposite, SWT.NONE);
		okButton.setText("OK");
		FormData formDataOk = new FormData();
		formDataOk.width = 70;
		formDataOk.right = new FormAttachment(cancelButton, -5);
		formDataOk.bottom = new FormAttachment(100, -5);
		okButton.setLayoutData(formDataOk);

		okButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {

				String input = constraintText.getText().trim();
				if (input.length() != 0) {

					// Check if the constraint ends with a ';' and
					// add a ';' when not.
					if (!input.endsWith(";")) {
						StringBuffer temp = new StringBuffer(input);
						temp.append(";");
						input = temp.toString();
					}
					try {
						if (constraint != null)
							featuremodel.removePropositionalNode(constraint);

						Node propNode = new FeatureModelReader(
								new FeatureModel()).readPropositionalString(
								input, featuremodel);

						featuremodel.addPropositionalNode(propNode);
						featuremodel.handleModelDataChanged();
						shell.dispose();
					} catch (UnsupportedModelException e1) {
						errorMarker.setImage(errorImage);
						errorMessage.setText(e1.getMessage());
					}
				} else {
					errorMarker.setImage(errorImage);
					errorMessage.setText("Enter a constraint");
				}

			}
		});
		cancelButton
				.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
					public void widgetSelected(
							org.eclipse.swt.events.SelectionEvent e) {

						shell.dispose();
					}
				});
	}

	/**
	 * 
	 */
	private void initHead() {

		headComposite = new Composite(shell, SWT.NONE);
		headComposite.setBackground(shell.getDisplay().getSystemColor(
				SWT.COLOR_WHITE));
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		headComposite.setLayoutData(gridData);

		GridLayout headLayout = new GridLayout();
		headLayout.numColumns = 3;
		headComposite.setLayout(headLayout);

		final Label capture = new Label(headComposite, SWT.NONE);
		FontData fontData = capture.getFont().getFontData()[0];
		Font font = new Font(shell.getDisplay(), new FontData(
				fontData.getName(), 11, SWT.NONE));
		capture.setFont(font);
		capture.setText("Constraint");
		capture.setBackground(shell.getDisplay()
				.getSystemColor(SWT.COLOR_WHITE));

		gridData = new GridData();
		gridData.horizontalSpan = 2;
		capture.setLayoutData(gridData);

		errorImage = ERROR_IMAGE;

		imageLabel = new Label(headComposite, SWT.RIGHT | SWT.DOWN);
		imageLabel.setImage(BANNER_IMAGE);
		imageLabel.setBackground(shell.getDisplay().getSystemColor(
				SWT.COLOR_WHITE));
		gridData = new GridData(GridData.FILL_VERTICAL | GridData.END
				| GridData.HORIZONTAL_ALIGN_END | GridData.VERTICAL_ALIGN_END);
		gridData.widthHint = 120;
		gridData.verticalSpan = 3;
		imageLabel.setLayoutData(gridData);

		errorMarker = new Label(headComposite, SWT.NONE);
		gridData = new GridData(GridData.BEGINNING);
		gridData.widthHint = 20;
		gridData.heightHint = 20;
		errorMarker.setBackground(shell.getDisplay().getSystemColor(
				SWT.COLOR_WHITE));
		errorMarker.setLayoutData(gridData);

		errorMessage = new Label(headComposite, SWT.SINGLE);
		errorMessage.setBackground(shell.getDisplay().getSystemColor(
				SWT.COLOR_WHITE));
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;

		errorMessage.setText(headerText);
		errorMessage.setLayoutData(gridData);
	}

	/**
	 * 
	 */
	private void initConstraintText() {
		Composite constraintTextComposite = new Composite(shell, SWT.NONE);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		constraintTextComposite.setLayoutData(gridData);
		FormLayout constraintTextLayout = new FormLayout();
		constraintTextComposite.setLayout(constraintTextLayout);

		Button validateButton = new Button(constraintTextComposite, SWT.NONE);
		validateButton.setText("Validate");
		FormData formDataValidateButton = new FormData();
		formDataValidateButton.width = 70;
		formDataValidateButton.right = new FormAttachment(100, -5);
		validateButton.setLayoutData(formDataValidateButton);

		constraintText = new Text(constraintTextComposite, SWT.SINGLE
				| SWT.BORDER);
		FormData formDataConstraintText = new FormData();
		formDataConstraintText.right = new FormAttachment(validateButton, -5);
		formDataConstraintText.left = new FormAttachment(0, 5);
		constraintText.setLayoutData(formDataConstraintText);
		constraintText.setText(initialConstraint);
		constraintText.addListener(SWT.FocusOut, new Listener() {

			@Override
			public void handleEvent(Event event) {

				x = constraintText.getSelection().x;
				y = constraintText.getSelection().y;

			}

		});

	}

	/**
 * 
 */
	private void initButtonGroup() {
		buttonGroup = new Group(shell, SWT.NONE);
		buttonGroup.setText("Operators");
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;
		buttonGroup.setLayoutData(gridData);
		GridLayout buttonGroupLayout = new GridLayout();
		buttonGroupLayout.numColumns = 7;
		buttonGroup.setLayout(buttonGroupLayout);

		for (int i = 0; i < OPERATOR_NAMES.length; i++) {

			final Button button = new Button(buttonGroup, SWT.PUSH);
			button.setText(OPERATOR_NAMES[i]);
			gridData = new GridData(GridData.FILL_HORIZONTAL);
			button.setLayoutData(gridData);
			button.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
				public void widgetSelected(
						org.eclipse.swt.events.SelectionEvent e) {
					StringBuffer temp = new StringBuffer(constraintText
							.getText());
					temp.delete(x, y);
					temp.insert(x > y ? y : x, " "
							+ button.getText().toLowerCase()
									.replaceAll(" ", "") + " ");
					constraintText.setText(temp.toString());
					constraintText.setFocus();
					constraintText.setSelection(constraintText.getCharCount());
				}
			});

		}

	}

	private void initFeatureGroup(final FeatureModel featuremodel) {
		featureGroup = new Group(shell, SWT.NONE);
		featureGroup.setText("Features");
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		featureGroup.setLayoutData(gridData);
		GridLayout featureGroupLayout = new GridLayout();
		featureGroupLayout.numColumns = 1;
		featureGroup.setLayout(featureGroupLayout);

		searchFeatureText = new StyledText(featureGroup, SWT.SINGLE | SWT.LEFT
				| SWT.BORDER);
		searchFeatureText.setText(FILTERTEXT);
		searchFeatureText.setForeground(shell.getDisplay().getSystemColor(
				SWT.COLOR_GRAY));
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		searchFeatureText.setLayoutData(gridData);

		Composite tableComposite = new Composite(featureGroup, SWT.NONE);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		tableComposite.setLayoutData(gridData);

		final TableViewer featureTableViewer = new TableViewer(tableComposite,
				SWT.BORDER | SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL);
		featureTable = featureTableViewer.getTable();
		featureTableViewer.setContentProvider(ArrayContentProvider
				.getInstance());
		TableViewerColumn viewerNameColumn = new TableViewerColumn(
				featureTableViewer, SWT.NONE);
		TableColumnLayout tableColumnLayout = new TableColumnLayout();
		tableComposite.setLayout(tableColumnLayout);
		tableColumnLayout.setColumnData(viewerNameColumn.getColumn(),
				new ColumnWeightData(100, 100, false));

		featureTableViewer.setComparator(new ViewerComparator() {

			@Override
			public int compare(Viewer viewer, Object feature1, Object feature2) {

				return ((Feature) feature1).getName().compareToIgnoreCase(
						((Feature) feature2).getName());
			}

		});

		viewerNameColumn.setLabelProvider(new CellLabelProvider() {
			@Override
			public void update(ViewerCell cell) {
				cell.setText(((Feature) cell.getElement()).getName());

			}
		});

		searchFeatureText.addListener(SWT.CHANGED, new Listener() {

			@Override
			public void handleEvent(Event event) {
				ViewerFilter searchFilter = new ViewerFilter() {

					@Override
					public boolean select(Viewer viewer, Object parentElement,
							Object element) {
						return ((Feature) element)
								.getName()
								.toLowerCase()
								.contains(
										searchFeatureText.getText()
												.toLowerCase());
					}

				};

				featureTableViewer.addFilter(searchFilter);

			}

		});
		searchFeatureText.addListener(SWT.FocusOut, new Listener() {

			@Override
			public void handleEvent(Event event) {
				if (searchFeatureText.getText().isEmpty()) {
					searchFeatureText.setText(FILTERTEXT);
					searchFeatureText.setForeground(shell.getDisplay()
							.getSystemColor(SWT.COLOR_GRAY));

				}

			}
		});
		searchFeatureText.addListener(SWT.FocusIn, new Listener() {

			@Override
			public void handleEvent(Event event) {
				if (searchFeatureText.getText().equals(FILTERTEXT))

					searchFeatureText.setText("");
				searchFeatureText.setForeground(shell.getDisplay()
						.getSystemColor(SWT.COLOR_BLACK));
			}

		});
		featureTableViewer.setInput(featuremodel.getFeatures());

		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessVerticalSpace = true;
		featureTable.setLayoutData(gridData);

		featureTable.addListener(SWT.MouseDoubleClick, new Listener() {
			@Override
			public void handleEvent(Event event) {
				TableItem[] selectedItem = featureTable.getSelection();
				StringBuffer temp = new StringBuffer(constraintText.getText());

				temp.delete(x, y);
				temp.insert(x > y ? y : x, " " + selectedItem[0].getText()
						+ " ");
				constraintText.setText(temp.toString());

				constraintText.setSelection(constraintText.getCharCount());
				searchFeatureText.setText(FILTERTEXT);
				searchFeatureText.setForeground(shell.getDisplay()
						.getSystemColor(SWT.COLOR_GRAY));
				constraintText.setFocus();
				featureTableViewer.resetFilters();
			}
		});

	}

}
