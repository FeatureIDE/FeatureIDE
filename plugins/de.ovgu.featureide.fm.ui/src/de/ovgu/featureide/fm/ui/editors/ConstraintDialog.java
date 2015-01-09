/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import java.util.ArrayList;
import java.util.Collection;
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
import org.eclipse.swt.events.KeyAdapter;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.layout.FillLayout;
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

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.Operator;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.ConstraintTextValidator.ValidationMessage;
import de.ovgu.featureide.fm.ui.editors.ConstraintTextValidator.ValidationResult;
import de.ovgu.featureide.fm.ui.editors.configuration.xxx.FunctionalInterfaces.IConsumer;
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
 * @author Marcus Pinnecke
 */
public class ConstraintDialog implements GUIDefaults {

	/**
	 * Mode in which the dialog runs. Use "UPDATE" if an exiting constraint should be
	 * edited and "CREATE" otherwise
	 * 
	 * @author Marcus Pinnecke
	 */
	public enum Mode {
		UPDATE, CREATE
	}

	/**
	 * Current constraint editing mode
	 */
	private Mode mode = Mode.CREATE;

	/**
	 * This is the panel on the top of the dialog. It contains the current 
	 * heading as well as a current state description.
	 * 
	 * @author Marcus Pinnecke
	 */
	public static class HeaderPanel {

		/**
		 * The panels background color
		 */
		private final Color panelBackgroundColor;

		/**
		 * The bubble is a circle of red, green, yellow or gray depending
		 * on the current dialog state.
		 * 
		 * {@link ConstraintDialog.HeaderPanel.BubbleColor}
		 */
		private Label bubble;

		/**
		 * Brief text what's the current mode for the dialog. This is more or less
		 * a visualization of "editing" or "creating" mode of this dialog.
		 */
		private Label headerLabel;
		
		/**
		 * Area which contains useful information about current progresses. It
		 * contains e.g. a list of dead features if any exists.
		 */
		private Text detailsLabel;

		/**
		 * Color types for the bubble
		 * {@link ConstraintDialog.HeaderPanel#bubble}
		 *  
		 * @author Marcus Pinnecke
		 */
		public enum BubbleColor {
			RED, GREEN, GRAY, YELLOW
		}

		/**
		 * Set current color for the bubble label show the user everything is okay (green),
		 * nothing happens until now (gray), everything is fine (green) or some
		 * error happens (red);
		 * 
		 * {@link ConstraintDialog.HeaderPanel.BubbleColor}
		 * {@link ConstraintDialog.HeaderPanel#bubble}
		 * 
		 * @param color The color to set
		 */
		public void setColor(BubbleColor color) {
			switch (color) {
			case RED:
				bubble.setImage(CIRLCE_RED);
				break;
			case GREEN:
				bubble.setImage(CIRLCE_GREEN);
				break;
			case YELLOW:
				bubble.setImage(CIRLCE_YELLOW);
				break;
			default:
				bubble.setImage(CIRLCE_GRAY);
				break;
			}
			bubble.redraw();
		}

		/**
		 * Sets the header text for this panel. This text should
		 * highlight the current dialogs state, e.g. editing an existing constraint.
		 * More information should be displayed in the details text are.
		 * 
		 * {@link ConstraintDialog.HeaderPanel#setDetails(String)}
		 * 
		 * @param text Text to display
		 */
		public void setHeader(String text) {
			headerLabel.setText(text.trim());
		}

		/**
		 * Set the details for this panel. This text should explain more in details
		 * what is going on or should provide useful hints or an error message. It
		 * can contain e.g. the list of dead features.
		 * 
		 * To set the header panels text, consider to use {@link #setHeader(String)}
		 * 
		 * @param text Text to display
		 */
		public void setDetails(String text) {
			detailsLabel.setText(text);
		}

		/**
		 * @return Gets the current headers text
		 */
		public String getHeader() {
			return headerLabel.getText();
		}

		/**
		 * @return Gets the current details text
		 */
		public String getDetails() {
			return detailsLabel.getText();
		}

		/**
		 * The composite to be used for placing the GUI elements
		 */
		private Composite headComposite;

		/**
		 * Constructs a new header panel to the shell. This panel contains a
		 * header text ({@link #setHeader(String)}), a details text ({@link #setDetails(String)})
		 * as well as a visualization of the currents dialog state styled as a colored bubble ({@link #setColor(BubbleColor)}).
		 * 
		 * By default a short info about possibilities with this dialog is display as details and
		 * that a new constraint will be created now. This should be altered with the methods
		 * above depending on the current state.
		 *   
		 * @param shell Shell to use
		 */
		public HeaderPanel(Shell shell) {
			headComposite = new Composite(shell, SWT.NONE);
			panelBackgroundColor = shell.getDisplay().getSystemColor(SWT.COLOR_WIDGET_BACKGROUND);

			headComposite.setBackground(panelBackgroundColor);
			GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
			headComposite.setLayoutData(gridData);

			GridLayout headLayout = new GridLayout();
			headLayout.numColumns = 2;
			headLayout.marginBottom = 7;
			headLayout.marginLeft = 10;
			headLayout.marginRight = 10;
			headLayout.marginTop = 7;
			headComposite.setLayout(headLayout);

			bubble = new Label(headComposite, SWT.NONE | SWT.TOP);
			bubble.setImage(CIRLCE_GRAY);

			headerLabel = new Label(headComposite, SWT.NONE);
			FontData fontData = headerLabel.getFont().getFontData()[0];
			Font fontActionLabel = new Font(shell.getDisplay(), new FontData(fontData.getName(), 12, SWT.BOLD));
			headerLabel.setFont(fontActionLabel);
			headerLabel.setText("Create new constraint");

			new Label(headComposite, SWT.NONE);		// adds an invisible separator to align details text field correctly

			detailsLabel = new Text(headComposite, SWT.WRAP | SWT.V_SCROLL);
			gridData = new GridData(GridData.FILL_BOTH);
			gridData.heightHint = 50;
			detailsLabel.setLayoutData(gridData);
			detailsLabel.setEditable(false);
			detailsLabel.setBackground(panelBackgroundColor);
			detailsLabel.setText("You can create or edit constraints with this dialog.");
		}
	}

	private static final String FILTERTEXT = "type filter text";

	/**
	 * The panel on the top of this dialog showing useful information and details as well as a
	 * colored bubble showing the current state.
	 */
	private HeaderPanel headerPanel;

	/**
	 * An object which contains several validation functionalities used in this dilog to
	 * check if a given constraint text is valid.
	 */
	private static final ConstraintTextValidator VALIDATOR = new ConstraintTextValidator();

	private Shell shell;

	private String initialConstraint;

	private Label errorMarker;
	private Text errorMessage;
	private Group featureGroup;
	private StyledText searchFeatureText;
	private Table featureTable;

	private Group buttonGroup;
	private Composite constraintTextComposite;
	private SimpleSyntaxHighlightEditor constraintText;
	private FeatureModel featureModel;
	private Button okButton;
	private Constraint constraint;

	private String defaultDetailsText;
	private String defaultHeaderText;

	private Button cancelButton;

	/**
	 * The dialogs title text
	 */
	private static final String DEFAULT_DIALOG_TITLE = "Constraint Dialog";

	/**
	 * 
	 * @param featuremodel
	 * @param constraint
	 */
	public ConstraintDialog(final FeatureModel featuremodel, final Constraint constraint) {
		this.constraint = constraint;
		this.featureModel = featuremodel;

		if (constraint == null) {
			defaultDetailsText = "Create Propositional Constraint";
			defaultHeaderText = "Create new Constraint";
			initialConstraint = "";
			mode = Mode.CREATE;

		} else {
			defaultDetailsText = "Edit Propositional Constraint";
			defaultHeaderText = "Edit your Constraint";

			initialConstraint = constraint.getNode().toString(NodeWriter.textualSymbols);

			mode = Mode.UPDATE;
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

		if (constraint != null)
			validate();

		updateDialogState(DialogState.SAVE_CHANGES_DISABLED);
	}

	/**
	 * initializes the shell
	 */
	private void initShell() {
		shell = new Shell(Display.getCurrent());
		shell.setText(DEFAULT_DIALOG_TITLE);
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
	private void initBottom(final FeatureModel featuremodel, final Constraint constraint) {
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
		helpButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				Program.launch("http://www.cs.utexas.edu/~schwartz/ATS/fopdocs/guidsl.html");
			}
		});
		FormData formDataHelp = new FormData();
		formDataHelp.left = new FormAttachment(0, 5);
		helpButtonBar.setLayoutData(formDataHelp);

		okButton = new Button(lastComposite, SWT.NONE);
		autoSetOkButtonText();
		FormData formDataOk = new FormData();
		formDataOk.width = 120;
		formDataOk.right = new FormAttachment(100, -5);
		formDataOk.bottom = new FormAttachment(100, -5);
		okButton.setLayoutData(formDataOk);

		cancelButton = new Button(lastComposite, SWT.NONE);
		cancelButton.setText("Cancel");
		FormData formDataCancel = new FormData();
		formDataCancel.width = 70;
		formDataCancel.right = new FormAttachment(okButton, -5);
		formDataCancel.bottom = new FormAttachment(100, -5);
		cancelButton.setLayoutData(formDataCancel);

		shell.setTabList(new Control[] { featureGroup, buttonGroup, constraintTextComposite, lastComposite });

		cancelButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {

				cancelButtonPressEvent();
			}
		});

		lastComposite.setTabList(new Control[] { okButton, cancelButton });

		okButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {

				okButtonPressEvent();

			}

		});
	}

	/**
	 * Logic for pressing okay-button. This is used because to be consistent to the {@link #cancelButtonPressEvent()} method. 
	 */
	private void okButtonPressEvent() {
		if (okButton.isEnabled()) {
			VALIDATOR.cancelValidation();
			closeShell();
		}
	}

	/**
	 * Logic for pressing cancel-button. This method is called when pressing ESC or hit the cancel button.
	 */
	private void cancelButtonPressEvent() {
		VALIDATOR.cancelValidation();
		shell.dispose();
	}

	/**
	 * The dialogs current state which correspond to the current validation process. Because some validation
	 * tests will take a long time span to be finished, the dialog has three states. 
	 * 
	 * SAVE_CHANGES_ENABLED
	 * means the dialog can be closed as regular. In this state everything is okay and the constraint is valid.
	 * 
	 * SAVE_CHANGES_DISABLED
	 * means the dialog can not be closed because there are syntax errors for the constraint text or 
	 * the validation process has finshed with an error found.
	 * 
	 * SAVE_CHANGES_DONT_MIND
	 * mean the dialog can be closed which is not recommended. However, some tests are running in this case.
	 * 
	 * @author Marcus Pinnecke
	 */
	private enum DialogState {
		SAVE_CHANGES_ENABLED, SAVE_CHANGES_DISABLED, SAVE_CHANGES_DONT_MIND
	}

	/**
	 * Depending on the current editing mode of this dialog the OK button text will be altered.
	 */
	private void autoSetOkButtonText() {
		okButton.setText((mode == Mode.UPDATE ? "Update" : "Create") + " Constraint");
	}
	
	/**
	 * Content proposal pop up.
	 */
	ContentProposalAdapter adapter;

	/**
	 * Updates the dialogs state, changing the default button and setting the text for this
	 * button depending on the current {@link ConstraintDialog.DialogState}
	 * 
	 * @param state The state to consider 
	 */
	private void updateDialogState(DialogState state) {
		switch (state) {
		case SAVE_CHANGES_ENABLED:
			okButton.setEnabled(true);
			shell.setDefaultButton(okButton);
			autoSetOkButtonText();
			break;
		case SAVE_CHANGES_DONT_MIND:
			okButton.setEnabled(true);
			shell.setDefaultButton(okButton);
			okButton.setText("Save anyway");
			break;
		default:
			okButton.setEnabled(false);
			shell.setDefaultButton(cancelButton);
			autoSetOkButtonText();
			break;
		}
	}

	/**
	 * initializes the upper part of the dialog
	 */
	private void initHead() {
		headerPanel = new HeaderPanel(shell);
		headerPanel.setHeader(defaultHeaderText);
		headerPanel.setDetails(defaultDetailsText);
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
		constraintText = new SimpleSyntaxHighlightEditor(constraintTextComposite, SWT.WRAP | SWT.BORDER | SWT.V_SCROLL, Operator.NAMES);

		adapter = new ContentProposalAdapter(constraintText, new SimpleSyntaxHighlighterConstraintContentAdapter(), new ConstraintContentProposalProvider(featureModel.getFeatureNames()), null, null);

		adapter.setAutoActivationDelay(500);
		adapter.setPopupSize(new Point(250, 85));

		adapter.setLabelProvider(new ConstraintProposalLabelProvider());
		FormData formDataConstraintText = new FormData();
		formDataConstraintText.right = new FormAttachment(100, -5);
		formDataConstraintText.left = new FormAttachment(0, 5);
		formDataConstraintText.height = 50;
		constraintText.setLayoutData(formDataConstraintText);
		constraintText.setText(initialConstraint);
		constraintText.setMargins(10, 5, 3, 5);
		constraintText.setPossibleWords (featureModel.getFeatureNames());

		constraintText.addKeyListener(new KeyAdapter() {
			public void keyReleased(KeyEvent event) {
				if (event.keyCode == SWT.ESC) {
					if (!adapter.isProposalPopupOpen()) {
						cancelButtonPressEvent();
					}					
				}
			}
		});

		constraintText.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				if (constraintText.getText().trim().isEmpty()) {
					headerPanel.setDetails("Please insert a constraint.");
					headerPanel.setColor(HeaderPanel.BubbleColor.GRAY);
					updateDialogState(DialogState.SAVE_CHANGES_DISABLED);
				}
				else validate();
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
				public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
					constraintText.copyIn(button.getText().toLowerCase(Locale.ENGLISH));
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

		searchFeatureText = new StyledText(featureGroup, SWT.SINGLE | SWT.LEFT | SWT.BORDER);
		searchFeatureText.setText(FILTERTEXT);
		searchFeatureText.setMargins(3, 5, 3, 5);
		searchFeatureText.setForeground(shell.getDisplay().getSystemColor(SWT.COLOR_GRAY));
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		searchFeatureText.setLayoutData(gridData);

		Composite tableComposite = new Composite(featureGroup, SWT.NONE);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		tableComposite.setLayoutData(gridData);

		final TableViewer featureTableViewer = new TableViewer(tableComposite, SWT.BORDER | SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL);
		featureTable = featureTableViewer.getTable();
		featureTableViewer.setContentProvider(new ArrayContentProvider());
		TableViewerColumn viewerNameColumn = new TableViewerColumn(featureTableViewer, SWT.NONE);
		TableColumnLayout tableColumnLayout = new TableColumnLayout();
		tableComposite.setLayout(tableColumnLayout);
		tableColumnLayout.setColumnData(viewerNameColumn.getColumn(), new ColumnWeightData(100, 100, false));

		featureTableViewer.setComparator(new ViewerComparator() {

			@Override
			public int compare(Viewer viewer, Object feature1, Object feature2) {

				return ((Feature) feature1).getName().compareToIgnoreCase(((Feature) feature2).getName());
			}

		});

		viewerNameColumn.setLabelProvider(new CellLabelProvider() {
			@Override
			public void update(ViewerCell cell) {
				cell.setText(((Feature) cell.getElement()).getName());
				cell.setImage(FEATURE_SYMBOL);
			}
		});

		searchFeatureText.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				if (!FILTERTEXT.equalsIgnoreCase(searchFeatureText.getText())) {
					ViewerFilter searchFilter = new ViewerFilter() {

						@Override
						public boolean select(Viewer viewer, Object parentElement, Object element) {
							return ((Feature) element).getName().toLowerCase(Locale.ENGLISH).contains(searchFeatureText.getText().toLowerCase(Locale.ENGLISH));
						}

					};
					featureTableViewer.addFilter(searchFilter);

				}
			}

		});

		searchFeatureText.addListener(SWT.FocusOut, new Listener() {

			@Override
			public void handleEvent(Event event) {
				if (searchFeatureText.getText().isEmpty()) {
					searchFeatureText.setText(FILTERTEXT);
					searchFeatureText.setForeground(shell.getDisplay().getSystemColor(SWT.COLOR_GRAY));

				}

			}
		});
		searchFeatureText.addListener(SWT.FocusIn, new Listener() {

			@Override
			public void handleEvent(Event event) {
				if (FILTERTEXT.equals(searchFeatureText.getText())) {
					searchFeatureText.setText("");
				}
				searchFeatureText.setForeground(shell.getDisplay().getSystemColor(SWT.COLOR_BLACK));
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
				constraintText.copyIn(selectedItem[0].getText());
			}
		});

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
		Collection<Feature> deadFeaturesBefore = null;
		FeatureModel clonedModel = model.clone();

		NodeReader nodeReader = new NodeReader();

		Node propNode = nodeReader.stringToNode(input, clonedModel.getFeatureNames());

		if (propNode != null) {
			if (constraint != null) {
				clonedModel.removeConstraint(constraint);
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

	public static final int VALIDATION_TIME_OUT = 1000;

	/**
	 * validates the current constraint in constraintText
	 * 
	 */
	private void validate() {
		headerPanel.setDetails("Checking constraint...");
		headerPanel.setColor(HeaderPanel.BubbleColor.GRAY);

		Display.getDefault().asyncExec(new Runnable() {

			@Override
			public void run() {
				ValidationResult result = VALIDATOR.validateSync(featureModel, constraintText.getText());
				
				constraintText.UnderlineEverything(result != ValidationResult.OK && constraintText.getUnknownWords().isEmpty());

				if (result == ValidationResult.OK) {
					VALIDATOR.validateAsync(constraint, VALIDATION_TIME_OUT, featureModel, constraintText.getText(), onCheckStarted, onVoidsModelCheckComplete, onFalseOptionalCheckComplete, onDeadFeatureCheckComplete, onIsRedundantCheckComplete, onCheckEnded, onIsTautology, onIsNotSatisfiable);
					updateDialogState(DialogState.SAVE_CHANGES_ENABLED);
				} else {
					String details = new String();

					if (result == ValidationResult.NOT_WELLFORMED) {						
						if (constraintText.getUnknownWords().isEmpty()) {
							details = "Your input constains syntax error.";							
						}
						else {
							int count = constraintText.getUnknownWords().size();
							details = "Constains contains " + count + " unknown feature name" + (count > 1 ? "s" : "") + ".";
						}						
					}
					else
						details = "";

					headerPanel.setDetails("Your constraint is invalid and can not be saved. " + details);
					headerPanel.setColor(HeaderPanel.BubbleColor.RED);

					updateDialogState(DialogState.SAVE_CHANGES_DISABLED);
				}
			}
		});
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
	 * closes the shell and adds new constraint to the feature model if possible
	 * 
	 * @param featureModel
	 * @param constraint
	 */
	private void closeShell() {
		NodeReader nodeReader = new NodeReader();
		String input = constraintText.getText().trim();

		if (input.length() == 0) {
			printHeaderError("constraint is empty");
			return;
		}

		Node propNode = nodeReader.stringToNode(input, featureModel.getFeatureNames());

		if (propNode == null) {
			printHeaderError(nodeReader.getErrorMessage());
			return;
		}
		if (!ConstraintTextValidator.isSatisfiable(input, VALIDATION_TIME_OUT)) {
			printHeaderWarning("constraint is unsatisfiable");
		}

		AbstractOperation op = null;
		if (constraint != null && featureModel.getConstraints().contains(constraint)) {
			int index = 0;
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

	/**
	 * Called when a validation test is just started. 
	 */
	private IConsumer<ValidationMessage> onCheckStarted = new IConsumer<ValidationMessage>() {
		@Override
		public void consume(ValidationMessage message) {
			updateDialogState(DialogState.SAVE_CHANGES_DONT_MIND);
			headerPanel.setDetails("Performing additional checks. This may take a while. Although it is not recommended, you can " + (mode == Mode.UPDATE ? "update" : "save") + " your constraint by clicking \"" + okButton.getText() + "\" before this process has ended.");
			headerPanel.setColor(HeaderPanel.BubbleColor.YELLOW);
		}
	};

	/**
	 * Called when the validation test for "voids model" has completed 
	 */
	private IConsumer<ValidationMessage> onVoidsModelCheckComplete = new IConsumer<ValidationMessage>() {
		@Override
		public void consume(ValidationMessage message) {
			if (message.validationResult != ValidationResult.OK) {
				headerPanel.setDetails("Your constraint voids the model");
				headerPanel.setColor(HeaderPanel.BubbleColor.RED);
				updateDialogState(DialogState.SAVE_CHANGES_DISABLED);
			}
		}
	};

	/**
	 * Called when the validation test for "false optional" has completed 
	 */
	private IConsumer<ValidationMessage> onFalseOptionalCheckComplete = new IConsumer<ValidationMessage>() {
		@Override
		public void consume(ValidationMessage message) {
			if (message.validationResult != ValidationResult.OK) {
				headerPanel.setDetails("Your constraint leads to false optional features.\n\n" + message.details);
				headerPanel.setColor(HeaderPanel.BubbleColor.RED);
				updateDialogState(DialogState.SAVE_CHANGES_DISABLED);
			}
		}
	};

	/**
	 * Called when the validation test for "dead features" has completed 
	 */
	private IConsumer<ValidationMessage> onDeadFeatureCheckComplete = new IConsumer<ValidationMessage>() {
		@Override
		public void consume(ValidationMessage message) {
			if (message.validationResult != ValidationResult.OK) {
				headerPanel.setDetails("Your constraint leads to dead features.\n\n" + message.details);
				headerPanel.setColor(HeaderPanel.BubbleColor.RED);
				updateDialogState(DialogState.SAVE_CHANGES_DISABLED);
			}
		}
	};

	/**
	 * Called when the validation test for "redundant check" has completed 
	 */
	private IConsumer<ValidationMessage> onIsRedundantCheckComplete = new IConsumer<ValidationMessage>() {
		@Override
		public void consume(ValidationMessage message) {
			if (message.validationResult != ValidationResult.OK) {
				headerPanel.setDetails("Redundancy occurred inside your constraint.");
				headerPanel.setColor(HeaderPanel.BubbleColor.RED);
				updateDialogState(DialogState.SAVE_CHANGES_DISABLED);
			}
		}
	};

	/**
	 * Called when the validation test has finished 
	 */
	private IConsumer<ValidationMessage> onCheckEnded = new IConsumer<ValidationMessage>() {
		@Override
		public void consume(ValidationMessage message) {
			headerPanel.setDetails("Click \"" + (mode == Mode.UPDATE ? "Update" : "Create") + "\" to " + (mode == Mode.UPDATE ? "save your changes." : "add your new constraint."));
			headerPanel.setColor(HeaderPanel.BubbleColor.GREEN);
			updateDialogState(DialogState.SAVE_CHANGES_ENABLED);
		}
	};

	/**
	 * Called when the validation test for "tautology" has completed 
	 */
	private IConsumer<ValidationMessage> onIsTautology = new IConsumer<ValidationMessage>() {
		@Override
		public void consume(ValidationMessage message) {
			if (message.validationResult != ValidationResult.OK) {
				headerPanel.setDetails("Your constraint is a tautology.");
				headerPanel.setColor(HeaderPanel.BubbleColor.RED);
				updateDialogState(DialogState.SAVE_CHANGES_DISABLED);
			}
		}
	};

	/**
	 * Called when the validation test for "satisfiable test" has completed 
	 */
	private IConsumer<ValidationMessage> onIsNotSatisfiable = new IConsumer<ValidationMessage>() {
		@Override
		public void consume(ValidationMessage message) {
			if (message.validationResult != ValidationResult.OK) {
				headerPanel.setDetails("Your constraint is not satisfiable.");
				headerPanel.setColor(HeaderPanel.BubbleColor.RED);
				updateDialogState(DialogState.SAVE_CHANGES_DISABLED);
			}
		}
	};
}
