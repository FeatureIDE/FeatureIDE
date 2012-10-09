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
package de.ovgu.featureide.fm.ui.editors;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.AbstractOperation;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.jface.fieldassist.ContentProposalAdapter;
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
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.layout.FormLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.program.Program;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Monitor;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;
import org.eclipse.ui.PlatformUI;
import org.prop4j.Node;
import org.prop4j.NodeReader;
import org.prop4j.NodeWriter;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.Operator;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ConstraintCreateOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ConstraintEditOperation;

/**
 * A simple editor for propositional constraints written below the feature
 * diagram.
 * 
 * @author Christian Becker
 * @author Thomas Thuem
 * @author David Broneske
 * @author Fabian Benduhn
 */

public class ConstraintDialog implements GUIDefaults {


	
	private static final String FILTERTEXT = "type filter text";
	private Shell shell;
	
	private String initialConstraint;

	private Label errorMarker;
	private Text errorMessage;
	private String titleText;
	private String headerText;
	private Group featureGroup;
	private StyledText searchFeatureText;
	private Table featureTable;

	private Group buttonGroup;
	private Composite constraintTextComposite;
	private Text constraintText;
	private FeatureModel featureModel;
	private int x, y;
	private Button okButton;
	private Constraint constraint;
	
	/**
	 * 
	 * @param featuremodel
	 * @param constraint
	 */
	public ConstraintDialog(final FeatureModel featuremodel,
			final Constraint constraint) {
		this.constraint = constraint;
		this.featureModel = featuremodel;

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
		printHeaderText(headerText);
		constraintText.setFocus();
		constraintText.setSelection(constraintText.getCharCount());
		shell.open();
		if (constraint != null)
			validate();
	}

	/**
	 * initializes the shell
	 */
	private void initShell() {
		shell = new Shell(Display.getCurrent());
		shell.setText(titleText);
		shell.setImage(FEATURE_SYMBOL);
		shell.setSize(500, 585);
		GridLayout shellLayout = new GridLayout();
		shellLayout.marginWidth = 0;
		shellLayout.marginHeight = 0;
		shell.setLayout(shellLayout);

		Monitor primary = shell.getDisplay().getPrimaryMonitor();
		Rectangle bounds = primary.getBounds();
		Rectangle rect = shell.getBounds();
		int x = bounds.x + (bounds.width - rect.width) / 2;
		int y = bounds.y + (bounds.height - rect.height) / 2;
		shell.setLocation(x, y);
		shell.addListener(SWT.Traverse, new Listener() {
			public void handleEvent(Event event) {
				if (event.detail == SWT.TRAVERSE_ESCAPE) {

					shell.close();

				}
			}
		});
	}

	/**
	 * initializes the bottom part of the dialog
	 * 
	 * @param featuremodel
	 * @param constraint
	 */
	private void initBottom(final FeatureModel featuremodel,
			final Constraint constraint) {
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);

		Composite lastComposite = new Composite(shell, SWT.NONE);
		lastComposite.setLayoutData(gridData);

		FormLayout lastCompositeLayout = new FormLayout();
		lastCompositeLayout.marginHeight = 5;
		lastCompositeLayout.marginTop = 85;
		lastCompositeLayout.marginWidth = 5;
		lastComposite.setLayout(lastCompositeLayout);
		ToolBar helpButtonBar = new ToolBar(lastComposite, SWT.FLAT);
		ToolItem helpButton = new ToolItem(helpButtonBar, SWT.NONE);
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

		Button cancelButton = new Button(lastComposite, SWT.NONE);
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
		shell.setTabList(new Control[] { featureGroup, buttonGroup,
				constraintTextComposite, lastComposite });

		lastComposite.setTabList(new Control[] { okButton, cancelButton });
		okButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {

				closeShell();

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
	 * initializes the upper part of the dialog
	 */
	private void initHead() {
		Composite headComposite = new Composite(shell, SWT.NONE);
		headComposite.setBackground(shell.getDisplay().getSystemColor(SWT.COLOR_WHITE));
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
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
		Label imageLabel = new Label(headComposite, SWT.RIGHT | SWT.DOWN);
		imageLabel.setImage(BANNER_IMAGE);
		imageLabel.setBackground(shell.getDisplay().getSystemColor(	SWT.COLOR_WHITE));
		gridData = new GridData(GridData.FILL_VERTICAL | GridData.END
				| GridData.HORIZONTAL_ALIGN_END | GridData.VERTICAL_ALIGN_END);
		gridData.widthHint = 90;
		gridData.verticalSpan = 3;
		imageLabel.setLayoutData(gridData);

		errorMarker = new Label(headComposite, SWT.NONE);
		gridData = new GridData(GridData.BEGINNING);
		gridData.widthHint = 20;
		gridData.heightHint = 20;
		gridData.verticalSpan = 2;
		errorMarker.setBackground(shell.getDisplay().getSystemColor(
				SWT.COLOR_WHITE));
		errorMarker.setLayoutData(gridData);

		errorMessage = new Text(headComposite, SWT.MULTI);
		errorMessage.setEditable(false);
		errorMessage.setBackground(shell.getDisplay().getSystemColor(
				SWT.COLOR_WHITE));
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		gridData.verticalSpan = 2;

		errorMessage.setLayoutData(gridData);
	}

	/**
	 * initializes the Text containing the constraint
	 */
	private void initConstraintText() {
		constraintTextComposite = new Composite(shell, SWT.NONE);
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);

		constraintTextComposite.setLayoutData(gridData);
		FormLayout constraintTextLayout = new FormLayout();
		constraintTextComposite.setLayout(constraintTextLayout);
		constraintText = new Text(constraintTextComposite, SWT.SINGLE
				| SWT.BORDER);

		ContentProposalAdapter adapter = new ContentProposalAdapter(
				constraintText, new ConstraintContentAdapter(),
				new ConstraintContentProposalProvider(
						featureModel.getFeatureNames()), null, null);

		adapter.setAutoActivationDelay(500);
		adapter.setPopupSize(new Point(250, 85));
		adapter.setLabelProvider(new ConstraintProposalLabelProvider());
		FormData formDataConstraintText = new FormData();
		formDataConstraintText.right = new FormAttachment(100, -5);
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

		constraintText.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				validate();

			}

		});

	}

	/**
	 * initializes the Group containing the operator buttons
	 */
	private void initButtonGroup() {
		buttonGroup = new Group(shell, SWT.NONE);
		buttonGroup.setText("Operators");
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;
		buttonGroup.setLayoutData(gridData);
		GridLayout buttonGroupLayout = new GridLayout();
		buttonGroupLayout.numColumns = 7;
		buttonGroup.setLayout(buttonGroupLayout);

		for (int i = 0; i < Operator.NAMES.length; i++) {

			final Button button = new Button(buttonGroup, SWT.PUSH);
			button.setText(Operator.NAMES[i]);
			gridData = new GridData(GridData.FILL_HORIZONTAL);
			button.setLayoutData(gridData);
			button.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
				public void widgetSelected(
						org.eclipse.swt.events.SelectionEvent e) {
					StringBuilder temp = new StringBuilder(constraintText
							.getText());
					temp.delete(x, y);
					temp.insert(x > y ? y : x, /*
												 * " " +
												 */button.getText().toLowerCase(Locale.ENGLISH) + " "
							
					/* .replaceAll(" ", "") + " " */);
					constraintText.setText(temp.toString()); //NodeReader.reduceWhiteSpaces(temp.toString()));
					constraintText.setFocus();
					constraintText.setSelection(constraintText.getCharCount());

					validate();
				}
			});

		}

	}

	/**
	 * initializes the group containing the searchText and featureTable
	 * 
	 * @param featuremodel
	 */
	private void initFeatureGroup(final FeatureModel featuremodel) {
	
		featureGroup = new Group(shell, SWT.NONE);
		featureGroup.setText("Features");
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
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
		featureTableViewer.setContentProvider(new ArrayContentProvider());
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

		searchFeatureText.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				ViewerFilter searchFilter = new ViewerFilter() {

					@Override
					public boolean select(Viewer viewer, Object parentElement,
							Object element) {
						return ((Feature) element)
								.getName()
								.toLowerCase(Locale.ENGLISH)
								.contains(
										searchFeatureText.getText()
												.toLowerCase(Locale.ENGLISH));
					}

				};
				if (!searchFeatureText.getText().equalsIgnoreCase(FILTERTEXT)) {
					featureTableViewer.addFilter(searchFilter);

				}
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
		
		featureTableViewer.setInput(featureModel.getFeatures());

		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessVerticalSpace = true;
		featureTable.setLayoutData(gridData);

		featureTable.addListener(SWT.MouseDoubleClick, new Listener() {
			@Override
			public void handleEvent(Event event) {
				TableItem[] selectedItem = featureTable.getSelection();
				StringBuilder temp = new StringBuilder(constraintText.getText());

				temp.delete(x, y);
				if (selectedItem.length > 0) {
					temp.insert(x > y ? y : x, " " + (selectedItem[0].getText().contains(" ")||Operator.isOperatorName(selectedItem[0].getText()) ? "\"" + selectedItem[0].getText() + "\"" : selectedItem[0].getText())
							+ " ");
					
				}
				constraintText.setText(temp.toString()); //NodeReader.reduceWhiteSpaces(temp.toString()));

				constraintText.setSelection(constraintText.getCharCount());
				searchFeatureText.setText(FILTERTEXT);
				searchFeatureText.setForeground(shell.getDisplay()
						.getSystemColor(SWT.COLOR_GRAY));
				constraintText.setFocus();
				featureTableViewer.resetFilters();

				validate();
			}
		});

	}

	/**
	 * returns true if constraint is satisfiable otherwise false
	 * 
	 * @param constraint
	 *            the constraint to be evaluated
	 * @param timeout
	 *            timeout in ms
	 */
	public boolean isSatisfiable(String constraint, int timeout) 
	{
		NodeReader nodeReader = new NodeReader();
		SatSolver satsolver = new SatSolver(nodeReader.stringToNode(constraint).clone(), timeout);
		try 
		{
			return satsolver.isSatisfiable();
		} catch (TimeoutException e) 
		{
			FMUIPlugin.getDefault().logError(e);
			return true;
		}

	}

	/**
	 * returns true if the constraint is always true
	 * 
	 * @param constraint
	 *            the constraint to be evaluated
	 * @param timeout
	 *            timeout in ms
	 * 
	 */
	public boolean isTautology(String constraint, int timeout) {
		NodeReader nodeReader = new NodeReader();
		Node node = nodeReader.stringToNode(constraint);

		SatSolver satsolver = new SatSolver(new Not(node.clone()), timeout);

		try {
			return !satsolver.isSatisfiable();
		} catch (TimeoutException e) {

			return true;
		}

	}

	/**
	 * returns true if the constraint causes the feature model to be void
	 * otherwise false
	 * 
	 * @param input
	 *            constraint to be evaluated
	 * @param model
	 *            the feature model
	 * 
	 *            * @throws TimeoutException
	 */
	public boolean voidsModel(String input, FeatureModel model)
			throws TimeoutException {

		if (!model.getAnalyser().isValid()) {

			return false;
		}
		if (input.length() == 0) {

			return false;
		}
		FeatureModel clonedModel = model.clone();
		NodeReader nodeReader = new NodeReader();

		List<String> featureList = new ArrayList<String>(
				clonedModel.getFeatureNames());
		Node propNode = nodeReader.stringToNode(input, featureList);
		if (propNode != null) {
			if (constraint != null) {
				clonedModel.removePropositionalNode(constraint);
			}
			clonedModel.addPropositionalNode(propNode);
			clonedModel.handleModelDataChanged();
		}

		return (!clonedModel.getAnalyser().isValid());

	}

	/**
	 * returns a List of all features that are caused to be dead by the
	 * constraint input
	 * 
	 * @param input
	 *            constraint to be evaluated
	 * @param model
	 *            the feature model
	 * @return List of all dead Features, empty if no feature is caused to be
	 *         dead
	 */
	public List<Feature> getDeadFeatures(String input, FeatureModel model) {
		List<Feature> deadFeaturesBefore = null;
		FeatureModel clonedModel = model.clone();

		NodeReader nodeReader = new NodeReader();

		List<String> featureList = new ArrayList<String>(
				clonedModel.getFeatureNames());
		Node propNode = nodeReader.stringToNode(input, featureList);

		if (propNode != null) {
			if (constraint != null) {
				clonedModel.removePropositionalNode(constraint);
			}
			deadFeaturesBefore = clonedModel.getAnalyser().getDeadFeatures();
			clonedModel.addPropositionalNode(propNode);
			clonedModel.handleModelDataChanged();
		}

		List<Feature> deadFeaturesAfter = new ArrayList<Feature>();
		for (Feature l : clonedModel.getAnalyser().getDeadFeatures()) {
			if (!deadFeaturesBefore.contains(l)) {
				deadFeaturesAfter.add(l);

			}
		}
		return deadFeaturesAfter;
	}
	
	public List<Feature> getFalseOptional(String input, FeatureModel model){
		List<Feature> list = new ArrayList<Feature>();
		FeatureModel clonedModel = model.clone();

		NodeReader nodeReader = new NodeReader();

		List<String> featureList = new ArrayList<String>(
				clonedModel.getFeatureNames());
		Node propNode = nodeReader.stringToNode(input, featureList);
		
		for (Feature feature : model.getFeatures()){
			if (input.contains(feature.getName())){
				if (feature.getFeatureStatus() != FeatureStatus.FALSE_OPTIONAL){
					clonedModel.addPropositionalNode(propNode);
					clonedModel.getAnalyser().analyzeFeatureModel(null);
					if (clonedModel.getFeature(feature.getName())
							.getFeatureStatus() == FeatureStatus.FALSE_OPTIONAL && !list.contains(feature)) 
								list.add(feature);
				}
			}
		}
		
		return list;
	}
	
	public String getFalseOptionalString (List<Feature> list){
		String listString = list.toString();
		String featureString = "Constraint causes the following features to be false optional: " + '\n';		
		return featureString + listString.substring(1, listString.length()-1);
	}

	/**
	 * validates the current constraint in constraintText
	 * 
	 */
	private boolean validate() {
		NodeReader nodereader = new NodeReader();
		String con = constraintText.getText().trim();
		boolean isWellformed = nodereader.isWellFormed(con,
				new ArrayList<String>(featureModel.getFeatureNames()));

		if (!isWellformed) {
			printHeaderError(nodereader.getErrorMessage());
			return false;
		}

		if (isTautology(con, 1000)) {

			printHeaderWarning("constraint is a tautology");
			return false;
		}
		if (!isSatisfiable(con, 1000)) {

			printHeaderWarning("constraint is unsatisfiable");
			return false;
		}
		try {
			if (featureModel.getAnalyser().isValid() && voidsModel(con, featureModel)) {

				printHeaderWarning("constraint makes model void");
				return false;
			}
		} catch (TimeoutException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		
		List<Feature> deadFeatures = getDeadFeatures(con, featureModel);
		if (!deadFeatures.isEmpty()) {
			printHeaderWarning(getDeadFeatureString(deadFeatures));
			return false;
		}

		
		List<Feature> falseOptionalFeatures = getFalseOptional(con, featureModel);
		if (!falseOptionalFeatures.isEmpty()){
			printHeaderWarning(getFalseOptionalString(falseOptionalFeatures));
			return false;
		}		

		try {
			if (featureModel.getAnalyser().isValid() && redundant(con)) {
				printHeaderWarning("The constraint does not change the product line.");
				return true;
			}
		} catch (TimeoutException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		
		printHeaderText(headerText);
		return true;
	}

	/**
	 * Tests if the {@link Constraint} will change the product line. 
	 * @param constraint The actual {@link Constraint}
	 * @return <code>true</code> if the {@link Constraint} is redundant
	 */
	private boolean redundant(String constraint) {
		if (constraint.length() == 0) {
			return false;
		}
		FeatureModel clonedModel = featureModel.clone();
		List<String> featureList = new ArrayList<String>(
				clonedModel.getFeatureNames());
		Node propNode = new NodeReader().stringToNode(constraint, featureList);
		clonedModel.addPropositionalNode(propNode);
		if (new ModelComparator(20000).compare(featureModel, clonedModel) == Comparison.REFACTORING) {
			return true;
		}
		return false;
	}

	/**
	 * returns a String to be displayed in the dialog header contains the list
	 * of dead features
	 * 
	 * @param deadFeatures
	 *            List of dead Features
	 * */
	private String getDeadFeatureString(List<Feature> deadFeatures) {
		StringBuilder featureString = new StringBuilder();
		featureString.append("Constraint causes the following features to be dead: ");
		int count = 0;
		int featureCount = 0;
		boolean isNewLine = false;
		for (Feature l : deadFeatures) {
			count = count + l.toString().length() + 2;

			if (isNewLine == false && count > 35) {
				featureString.append('\n');
				isNewLine = true;
			}
			if (count < 90) {
				featureString.append(l);
				if (featureCount < deadFeatures.size() - 1)
					featureString.append(", ");
				featureCount++;

			}
			if (deadFeatures.indexOf(l) == deadFeatures.size() - 1) {

			}

		}
		if (featureCount < deadFeatures.size()) {
			featureString.append("...");
		}
		return featureString.toString();
	}

	/**
	 * displays a warning in the header
	 * 
	 * @param message
	 *            message to be displayed
	 */
	private void printHeaderWarning(String message) {
		okButton.setEnabled(true);
		errorMarker.setImage(WARNING_IMAGE);
		errorMarker.setVisible(true);
		errorMessage.setText(message);
		errorMessage.pack();
	}

	/**
	 * displays an error in the header
	 * 
	 * @param message
	 *            message to be displayed
	 */
	private void printHeaderError(String message) {
		okButton.setEnabled(false);
		errorMarker.setImage(ERROR_IMAGE);
		errorMarker.setVisible(true);
		errorMessage.setText(message);
	}

	/**
	 * displays a Text in the header
	 * 
	 * @param message
	 *            message to be displayed
	 */
	private void printHeaderText(String message) {
		okButton.setEnabled(true);
		errorMarker.setVisible(false);
		errorMessage.setText(message);

	}

	/**
	 * closes the shell and adds new constraint to the feature model if possible
	 * 
	 * @param featureModel
	 * @param constraint
	 */
	private void closeShell() {
		NodeReader nodeReader = new NodeReader();
		String input = constraintText.getText().trim();

		if (input.length() == 0) 
		{
			printHeaderError("constraint is empty");
			return;
		}

		List<String> featureList = new ArrayList<String>(
				featureModel.getFeatureNames());
		Node propNode = nodeReader.stringToNode(input, featureList);
		
		
		if (propNode == null) {
			printHeaderError(nodeReader.getErrorMessage());
			return;
		}
		if (!isSatisfiable(input, 1000)) {
			printHeaderWarning("constraint is unsatisfiable");			
		}
		
		int index = 0;
		AbstractOperation op = null;
		if (constraint != null && featureModel.getConstraints().contains(constraint)) {
			for (Constraint c : featureModel.getConstraints()) {
				if (c == constraint) {
					op = new ConstraintEditOperation(propNode, featureModel, index);
					break;
				}
				index++;
			}	
		}
		if (op == null) {
			op = new ConstraintCreateOperation(propNode, featureModel);
		}
		op.addContext((IUndoContext) featureModel.getUndoContext());
		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}

		shell.dispose();

	}
}
