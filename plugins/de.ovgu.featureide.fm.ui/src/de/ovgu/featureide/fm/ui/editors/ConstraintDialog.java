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
package de.ovgu.featureide.fm.ui.editors;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADD_YOUR_NEW_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.BEFORE_THIS_PROCESS_HAS_ENDED;
import static de.ovgu.featureide.fm.core.localization.StringTable.CANCEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHECKING_CONSTRAINT___;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_CONTAINS_ONE_UNKNOWN_FEATURE_NAME_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_DIALOG;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_UNSATISFIABLE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_NEW_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_PROPOSITIONAL_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.EDIT_PROPOSITIONAL_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.EDIT_YOUR_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.OPERATORS;
import static de.ovgu.featureide.fm.core.localization.StringTable.PLEASE_INSERT_A_CONSTRAINT_;
import static de.ovgu.featureide.fm.core.localization.StringTable.REDUNDANCY_OCCURRED_INSIDE_YOUR_CONSTRAINT_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SAVE;
import static de.ovgu.featureide.fm.core.localization.StringTable.SAVE_ANYWAY;
import static de.ovgu.featureide.fm.core.localization.StringTable.SAVE_YOUR_CHANGES;
import static de.ovgu.featureide.fm.core.localization.StringTable.TYPE_FILTER_TEXT;
import static de.ovgu.featureide.fm.core.localization.StringTable.UPDATE;
import static de.ovgu.featureide.fm.core.localization.StringTable.YOUR_CONSTRAINT_IS_A_TAUTOLOGY_;
import static de.ovgu.featureide.fm.core.localization.StringTable.YOUR_CONSTRAINT_IS_NOT_SATISFIABLE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.YOUR_CONSTRAINT_VOIDS_THE_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.YOUR_INPUT_CONSTAINS_SYNTAX_ERRORS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.YOU_CAN_CREATE_OR_EDIT_CONSTRAINTS_WITH_THIS_DIALOG_;

import java.util.List;
import java.util.Locale;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.AbstractOperation;
import org.eclipse.jface.bindings.keys.KeyStroke;
import org.eclipse.jface.bindings.keys.ParseException;
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
import org.eclipse.swt.graphics.Color;
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

import de.ovgu.featureide.fm.core.Operator;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IConsumer;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.ConstraintTextValidator.ValidationMessage;
import de.ovgu.featureide.fm.ui.editors.ConstraintTextValidator.ValidationResult;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.CreateConstraintOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.EditConstraintOperation;

/**
 * A simple editor for propositional constraints written below the feature diagram.
 *
 * @author Christian Becker
 * @author Thomas Thuem
 * @author David Broneske
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class ConstraintDialog implements GUIDefaults {

	/**
	 * The dialogs current state which correspond to the current validation process. Because some validation tests will take a long time span to be finished,
	 * the dialog has three states.
	 *
	 * SAVE_CHANGES_ENABLED means the dialog can be closed as regular. In this state everything is okay and the constraint is valid.
	 *
	 * SAVE_CHANGES_DISABLED means the dialog can not be closed because there are syntax errors for the constraint text or the validation process has finished
	 * with an error found.
	 *
	 * SAVE_CHANGES_DONT_MIND mean the dialog can be closed which is not recommended. However, some tests are running in this case.
	 *
	 * @author Marcus Pinnecke
	 */
	private enum DialogState {
		SAVE_CHANGES_ENABLED, SAVE_CHANGES_DISABLED, SAVE_CHANGES_DONT_MIND
	}

	/**
	 * This is the panel on the top of the dialog. It contains the current heading as well as a current state description.
	 *
	 * @author Marcus Pinnecke
	 */
	public static class HeaderPanel {

		/**
		 * Image types for description inside header panel {@link ConstraintDialog.HeaderPanel#headerDescriptionImageLabel}
		 *
		 * @author Marcus Pinnecke
		 */
		public enum HeaderDescriptionImage {
			ERROR, WARNING, NONE
		}

		private static final String STRING_HEADER_LABEL_DEFAULT = CREATE_NEW_CONSTRAINT;

		private static final String STRING_HEADER_DETAILS_DEFAULT = YOU_CAN_CREATE_OR_EDIT_CONSTRAINTS_WITH_THIS_DIALOG_;

		/**
		 * The panels background color
		 */
		private final Color panelBackgroundColor;

		/**
		 * The actual image of the headers description label
		 *
		 * {@link ConstraintDialog.HeaderPanel.HeaderDescriptionImage}
		 */
		private final Label headerDescriptionImageLabel;

		/**
		 * Brief text what's the current mode for the dialog. This is more or less a visualization of EDITING or "creating" mode of this dialog.
		 */
		private final Label headerLabel;

		/**
		 * Area which contains useful information about current progresses. It contains e.g. a list of dead features if any exists.
		 */
		private final Text detailsLabel;

		/**
		 * The composite to be used for placing the GUI elements
		 */
		private final Composite headComposite;

		/**
		 * Constructs a new header panel to the shell. This panel contains a header text ({@link #setHeader(String)}), a details text (
		 * {@link #setDetails(String)}).
		 *
		 * By default a short info about possibilities with this dialog is display as details and that a new constraint will be created now. This should be
		 * altered with the methods above depending on the current state.
		 *
		 * @param shell Shell to use
		 */
		public HeaderPanel(Shell shell) {
			headComposite = new Composite(shell, SWT.NONE);
			panelBackgroundColor = shell.getDisplay().getSystemColor(SWT.COLOR_WIDGET_BACKGROUND);

			headComposite.setBackground(panelBackgroundColor);
			GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
			headComposite.setLayoutData(gridData);

			final GridLayout headLayout = new GridLayout();
			headLayout.numColumns = 2;
			headLayout.marginBottom = 7;
			headLayout.marginLeft = 10;
			headLayout.marginRight = 10;
			headLayout.marginTop = 7;
			headComposite.setLayout(headLayout);

			headerDescriptionImageLabel = new Label(headComposite, SWT.NONE | SWT.TOP);
			headerDescriptionImageLabel.setImage(null);

			headerLabel = new Label(headComposite, SWT.NONE);
			final FontData fontData = headerLabel.getFont().getFontData()[0];
			final Font fontActionLabel = new Font(shell.getDisplay(), new FontData(fontData.getName(), 12, SWT.BOLD));
			headerLabel.setFont(fontActionLabel);
			headerLabel.setText(STRING_HEADER_LABEL_DEFAULT);

			new Label(headComposite, SWT.NONE); // adds an invisible separator
												 // to align details text field
												 // correctly

			detailsLabel = new Text(headComposite, SWT.WRAP | SWT.V_SCROLL);
			gridData = new GridData(GridData.FILL_BOTH);
			gridData.heightHint = 50;
			detailsLabel.setLayoutData(gridData);
			detailsLabel.setEditable(false);
			detailsLabel.setBackground(panelBackgroundColor);

			setDetails(STRING_HEADER_DETAILS_DEFAULT, HeaderDescriptionImage.NONE);
		}

		/**
		 * @return Gets the current details text
		 */
		public String getDetails() {
			return detailsLabel.getText();
		}

		/**
		 * @return Gets the current headers text
		 */
		public String getHeader() {
			return headerLabel.getText();
		}

		/**
		 * Set the details for this panel. This text should explain more in details what is going on or should provide useful hints or an error message. It can
		 * contain e.g. the list of dead features.
		 *
		 * To set the header panels text, consider to use {@link #setHeader(String)}
		 *
		 * @param text Text to display
		 */
		public void setDetails(String text, HeaderDescriptionImage image) {
			detailsLabel.setText(text);
			setImage(image);
		}

		/**
		 * Sets the header text for this panel. This text should highlight the current dialogs state, e.g. editing an existing constraint. More information
		 * should be displayed in the details text are.
		 *
		 * {@link ConstraintDialog.HeaderPanel#setDetails(String)}
		 *
		 * @param text Text to display
		 */
		public void setHeader(String text) {
			headerLabel.setText(text.trim());
		}

		/**
		 * Set current image for the details text.
		 *
		 * {@link ConstraintDialog.HeaderPanel.HeaderDescriptionImage} {@link ConstraintDialog.HeaderPanel#headerDescriptionImageLabel}
		 *
		 * @param image The image to set
		 */
		private void setImage(HeaderDescriptionImage image) {
			switch (image) {
			case ERROR:
				headerDescriptionImageLabel.setImage(GUIDefaults.ERROR_IMAGE);
				break;
			case WARNING:
				headerDescriptionImageLabel.setImage(GUIDefaults.WARNING_IMAGE);
				break;
			default:
				headerDescriptionImageLabel.setImage(GUIDefaults.IMAGE_EMPTY);
				break;
			}
			headerDescriptionImageLabel.redraw();

		}
	}

	/**
	 * Mode in which the dialog runs. Use "UPDATE" if an exiting constraint should be edited and "CREATE" otherwise
	 *
	 * @author Marcus Pinnecke
	 */

	public enum Mode {
		UPDATE, CREATE
	}

	static class StringTable {

		static final String CONSTRAINT_VOIDS_MODEL = YOUR_CONSTRAINT_VOIDS_THE_MODEL;

		static final String CONSTRAINT_FALSE_OPTIONAL = "Your constraint leads to false optional features.\n\n%s";

		static final String CONSTRAINT_DEAD_FEATURES = "Your constraint leads to dead features.\n\n%s";

		static final String CONSTRAINT_REDUNDANCE = REDUNDANCY_OCCURRED_INSIDE_YOUR_CONSTRAINT_;

		static final String CONSTRAINT_CHECK_ENDED = "Click \"%s\" to %s .";

		static final String CONSTRAINT_TAUTOLOGY = YOUR_CONSTRAINT_IS_A_TAUTOLOGY_;

		static final String CONSTRAINT_NOT_SATISFIABLE = YOUR_CONSTRAINT_IS_NOT_SATISFIABLE_;

		static final String DEFAULT_DETAILS_NEW_CONSTRAINT = CREATE_PROPOSITIONAL_CONSTRAINT;

		static final String DEFAULT_HEADER_NEW_CONSTRAINT = "Create new Constraint";

		static final String DEFAULT_DETAILS_EDIT_CONSTRAINT = EDIT_PROPOSITIONAL_CONSTRAINT;

		static final String DEFAULT_HEADER_EDIT_CONSTRAINT = EDIT_YOUR_CONSTRAINT;

		static final String VERB_UPDATE = UPDATE;

		static final String VERB_CREATE = CREATE;

		static final String OK_BUTTON_TEXT = "%s Constraint";

		static final String SAVE_CHANGES = SAVE_YOUR_CHANGES;

		static final String ADD_NEW_CONSTRAINT = ADD_YOUR_NEW_CONSTRAINT;

		static final String VERB_SAVE = SAVE;

		static final String CONSTRAINT_IS_NOT_SATISFIABLE = CONSTRAINT_IS_UNSATISFIABLE;

		static final String HREF_HELP_LINK = "http://www.cs.utexas.edu/~schwartz/ATS/fopdocs/guidsl.html";

		static final String PLEASE_INSERT_CONSTRAINT = PLEASE_INSERT_A_CONSTRAINT_;

		static final String KEYSTROKE_SHORTCUT_FOR_PROPOSAL = "Ctrl+Space";

		static final String CHECKING_CONSTRAINTS = CHECKING_CONSTRAINT___;

		static final String CONSTRAINT_CONTAINS_SYNTAX_ERRORS = YOUR_INPUT_CONSTAINS_SYNTAX_ERRORS_;

		static final String CONSTRAINT_CONTAINS_UNKNOWN_FEATURE = CONSTRAINT_CONTAINS_ONE_UNKNOWN_FEATURE_NAME_;

		static final String CONSTRAINT_CONTAINS_UNKNOWN_FEATURES = "Constraint contains %s unknown feature names.";

		static final String CONSTRAINT_CONNOT_BE_SAVED = "Your constraint is invalid and can not be saved:\n%s";

	}

	/**
	 * Current constraint editing mode.
	 */
	private Mode mode = Mode.CREATE;

	private static final String FILTERTEXT = TYPE_FILTER_TEXT;

	/**
	 * The panel on the top of this dialog showing useful information and details.
	 */
	private HeaderPanel headerPanel;

	/**
	 * An object which contains several validation functionalities used in this dialog to check if a given constraint text is valid.
	 */
	private static final ConstraintTextValidator VALIDATOR = new ConstraintTextValidator();

	private Shell shell;

	private String initialConstraint;
	private Group featureGroup;
	private StyledText searchFeatureText;

	private Table featureTable;
	private Group buttonGroup;
	private Composite constraintTextComposite;
	private SimpleSyntaxHighlightEditor constraintText;
	private final IFeatureModel featureModel;
	private Button okButton;

	private final IConstraint constraint;
	private String defaultDetailsText;

	private String defaultHeaderText;

	private Button cancelButton;

	/**
	 * The dialogs title text.
	 */
	private static final String DEFAULT_DIALOG_TITLE = CONSTRAINT_DIALOG;

	/**
	 * Content proposal pop up.
	 */
	ContentProposalAdapter adapter;

	private final static int PROPOSAL_AUTO_ACTIVATION_DELAY = 500;

	public static final int VALIDATION_TIME_OUT = 1000;

	/**
	 * Called when a validation test is just started.
	 */
	private final IConsumer<ValidationMessage> onCheckStarted = new IConsumer<ValidationMessage>() {

		@Override
		public void invoke(ValidationMessage message) {
			updateDialogState(DialogState.SAVE_CHANGES_DONT_MIND);
			headerPanel.setDetails(String.format(BEFORE_THIS_PROCESS_HAS_ENDED,
					(mode == Mode.UPDATE ? StringTable.VERB_UPDATE.toLowerCase() : StringTable.VERB_SAVE), okButton.getText()),
					HeaderPanel.HeaderDescriptionImage.NONE);
		}
	};

	/**
	 * Called when the validation test for VOIDS_MODEL has completed.
	 */
	private final IConsumer<ValidationMessage> onVoidsModelCheckComplete = new IConsumer<ValidationMessage>() {

		@Override
		public void invoke(ValidationMessage message) {
			if (message.validationResult != ValidationResult.OK) {
				headerPanel.setDetails(StringTable.CONSTRAINT_VOIDS_MODEL, HeaderPanel.HeaderDescriptionImage.WARNING);
			}
		}
	};

	/**
	 * Called when the validation test for FALSE_OPTIONAL has completed.
	 */
	private final IConsumer<ValidationMessage> onFalseOptionalCheckComplete = new IConsumer<ValidationMessage>() {

		@Override
		public void invoke(ValidationMessage message) {
			if (message.validationResult != ValidationResult.OK) {
				headerPanel.setDetails(String.format(StringTable.CONSTRAINT_FALSE_OPTIONAL, message.details), HeaderPanel.HeaderDescriptionImage.WARNING);
			}
		}
	};

	/**
	 * Called when the validation test for DEAD_FEATURES has completed.
	 */
	private final IConsumer<ValidationMessage> onDeadFeatureCheckComplete = new IConsumer<ValidationMessage>() {

		@Override
		public void invoke(ValidationMessage message) {
			if (message.validationResult != ValidationResult.OK) {
				headerPanel.setDetails(String.format(StringTable.CONSTRAINT_DEAD_FEATURES, message.details), HeaderPanel.HeaderDescriptionImage.WARNING);
			}
		}
	};

	/**
	 * Called when the validation test for REDUNDANT_CHECK has completed.
	 */
	private final IConsumer<ValidationMessage> onIsRedundantCheckComplete = new IConsumer<ValidationMessage>() {

		@Override
		public void invoke(ValidationMessage message) {
			if (message.validationResult != ValidationResult.OK) {
				headerPanel.setDetails(StringTable.CONSTRAINT_REDUNDANCE, HeaderPanel.HeaderDescriptionImage.WARNING);
			}
		}
	};

	/**
	 * Called when the validation test has finished.
	 */
	private final IConsumer<ValidationMessage> onCheckEnded = new IConsumer<ValidationMessage>() {

		@Override
		public void invoke(ValidationMessage message) {
			headerPanel.setDetails(String.format(StringTable.CONSTRAINT_CHECK_ENDED, (mode == Mode.UPDATE ? StringTable.VERB_UPDATE : StringTable.VERB_CREATE),
					(mode == Mode.UPDATE ? StringTable.SAVE_CHANGES : StringTable.ADD_NEW_CONSTRAINT)), HeaderPanel.HeaderDescriptionImage.NONE);
			updateDialogState(DialogState.SAVE_CHANGES_ENABLED);
		}
	};

	/**
	 * Called when the validation test for "tautology" has completed.
	 */
	private final IConsumer<ValidationMessage> onIsTautology = new IConsumer<ValidationMessage>() {

		@Override
		public void invoke(ValidationMessage message) {
			if (message.validationResult != ValidationResult.OK) {
				headerPanel.setDetails(StringTable.CONSTRAINT_TAUTOLOGY, HeaderPanel.HeaderDescriptionImage.WARNING);
			}
		}
	};

	/**
	 * Called when the validation test for SATISFIABLE_TEST has completed.
	 */
	private final IConsumer<ValidationMessage> onIsNotSatisfiable = new IConsumer<ValidationMessage>() {

		@Override
		public void invoke(ValidationMessage message) {
			if (message.validationResult != ValidationResult.OK) {
				headerPanel.setDetails(StringTable.CONSTRAINT_NOT_SATISFIABLE, HeaderPanel.HeaderDescriptionImage.WARNING);
			}
		}
	};

	public ConstraintDialog(final IFeatureModel featuremodel, final IConstraint constraint) {
		this.constraint = constraint;
		featureModel = featuremodel;

		if (constraint == null) {
			defaultDetailsText = StringTable.DEFAULT_DETAILS_NEW_CONSTRAINT;
			defaultHeaderText = StringTable.DEFAULT_HEADER_NEW_CONSTRAINT;
			initialConstraint = "";
			mode = Mode.CREATE;

		} else {
			defaultDetailsText = StringTable.DEFAULT_DETAILS_EDIT_CONSTRAINT;
			defaultHeaderText = StringTable.DEFAULT_HEADER_EDIT_CONSTRAINT;

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

		if (constraint != null) {
			validate();
		}

		updateDialogState(DialogState.SAVE_CHANGES_DISABLED);
	}

	/**
	 * Depending on the current editing mode of this dialog the OK button text will be altered.
	 */
	private void autoSetOkButtonText() {
		okButton.setText(String.format(StringTable.OK_BUTTON_TEXT, (mode == Mode.UPDATE ? StringTable.VERB_UPDATE : StringTable.VERB_CREATE)));
	}

	/**
	 * Logic for pressing cancel-button. This method is called when pressing ESC or hit the cancel button.
	 */
	private void cancelButtonPressEvent() {
		VALIDATOR.cancelValidation();
		shell.dispose();
	}

	/**
	 * closes the shell and adds new constraint to the feature model if possible
	 *
	 * @param featureModel
	 * @param constraint
	 */
	private void closeShell() {
		final NodeReader nodeReader = new NodeReader();
		final String input = constraintText.getText().trim();
		final Node propNode = nodeReader.stringToNode(input, Functional.toList(FeatureUtils.extractFeatureNames(featureModel.getFeatures())));

		AbstractOperation op = null;
		if ((constraint != null) && featureModel.getConstraints().contains(constraint)) {
			for (final IConstraint c : featureModel.getConstraints()) {
				if (c == constraint) {
					op = new EditConstraintOperation(featureModel, c, propNode);
					break;
				}
			}
		}
		if (op == null) {
			op = new CreateConstraintOperation(propNode, featureModel);
		}
		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}

		shell.dispose();
	}

	/**
	 * Initializes the bottom part of the dialog
	 *
	 * @param featuremodel
	 * @param constraint
	 */
	private void initBottom(final IFeatureModel featuremodel, final IConstraint constraint) {
		final GridData gridData = new GridData(GridData.FILL_HORIZONTAL);

		final Composite lastComposite = new Composite(shell, SWT.NONE);
		lastComposite.setLayoutData(gridData);

		final FormLayout lastCompositeLayout = new FormLayout();
		lastCompositeLayout.marginHeight = 5;
		lastCompositeLayout.marginTop = 85;
		lastCompositeLayout.marginWidth = 5;
		lastComposite.setLayout(lastCompositeLayout);
		final ToolBar helpButtonBar = new ToolBar(lastComposite, SWT.FLAT);
		final ToolItem helpButton = new ToolItem(helpButtonBar, SWT.NONE);
		helpButton.setImage(HELP_IMAGE);
		helpButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {

			@Override
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
				Program.launch(StringTable.HREF_HELP_LINK);
			}
		});
		final FormData formDataHelp = new FormData();
		formDataHelp.left = new FormAttachment(0, 5);
		helpButtonBar.setLayoutData(formDataHelp);

		cancelButton = new Button(lastComposite, SWT.NONE);
		cancelButton.setText(CANCEL);
		final FormData formDataCancel = new FormData();
		formDataCancel.width = 70;
		formDataCancel.right = new FormAttachment(100, -5);
		formDataCancel.bottom = new FormAttachment(100, -5);

		okButton = new Button(lastComposite, SWT.NONE);
		autoSetOkButtonText();
		final FormData formDataOk = new FormData();
		formDataOk.width = 120;
		formDataOk.right = new FormAttachment(cancelButton, -5);
		formDataOk.bottom = new FormAttachment(100, -5);
		okButton.setLayoutData(formDataOk);

		cancelButton.setLayoutData(formDataCancel);

		shell.setTabList(new Control[] { featureGroup, buttonGroup, constraintTextComposite, lastComposite });

		cancelButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {

			@Override
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {

				cancelButtonPressEvent();
			}
		});

		lastComposite.setTabList(new Control[] { okButton, cancelButton });

		okButton.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {

			@Override
			public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {

				okButtonPressEvent();

			}

		});
	}

	/**
	 * Initializes the group containing the operator buttons.
	 */
	private void initButtonGroup() {
		buttonGroup = new Group(shell, SWT.NONE);
		buttonGroup.setText(OPERATORS);
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;
		buttonGroup.setLayoutData(gridData);
		final GridLayout buttonGroupLayout = new GridLayout();
		buttonGroupLayout.numColumns = 7;
		buttonGroup.setLayout(buttonGroupLayout);

		for (int i = 0; i < Operator.NAMES.length; i++) {

			final Button button = new Button(buttonGroup, SWT.PUSH);
			button.setText(Operator.NAMES[i]);
			gridData = new GridData(GridData.FILL_HORIZONTAL);
			button.setLayoutData(gridData);
			button.addSelectionListener(new org.eclipse.swt.events.SelectionAdapter() {

				@Override
				public void widgetSelected(org.eclipse.swt.events.SelectionEvent e) {
					constraintText.copyIn(button.getText().toLowerCase(Locale.ENGLISH));
				}

			});
		}
	}

	/**
	 * Initializes the text containing the constraint.
	 */
	private void initConstraintText() {
		constraintTextComposite = new Composite(shell, SWT.NONE);
		final GridData gridData = new GridData(GridData.FILL_HORIZONTAL);

		constraintTextComposite.setLayoutData(gridData);
		final FormLayout constraintTextLayout = new FormLayout();
		constraintTextComposite.setLayout(constraintTextLayout);
		constraintText = new SimpleSyntaxHighlightEditor(constraintTextComposite, SWT.SINGLE | SWT.H_SCROLL | SWT.BORDER, Operator.NAMES);

		setupContentProposal();

		final FormData formDataConstraintText = new FormData();
		formDataConstraintText.right = new FormAttachment(100, -5);
		formDataConstraintText.left = new FormAttachment(0, 5);
		// formDataConstraintText.height = 50;
		constraintText.setLayoutData(formDataConstraintText);
		constraintText.setText(initialConstraint);
		constraintText.setMargins(10, 5, 3, 5);
		constraintText.setPossibleWords(Functional.toSet(FeatureUtils.extractFeatureNames(featureModel.getFeatures())));

		constraintText.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				if (constraintText.getText().trim().isEmpty()) {
					headerPanel.setDetails(StringTable.PLEASE_INSERT_CONSTRAINT, HeaderPanel.HeaderDescriptionImage.NONE);
					updateDialogState(DialogState.SAVE_CHANGES_DISABLED);
				} else {
					validate();
				}
			}
		});

	}

	/**
	 * Initializes the group containing the searchText and featureTable.
	 *
	 * @param featuremodel
	 */
	private void initFeatureGroup(final IFeatureModel featuremodel) {
		featureGroup = new Group(shell, SWT.NONE);
		featureGroup.setText("Features");
		GridData gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		featureGroup.setLayoutData(gridData);
		final GridLayout featureGroupLayout = new GridLayout();
		featureGroupLayout.numColumns = 1;
		featureGroup.setLayout(featureGroupLayout);

		searchFeatureText = new StyledText(featureGroup, SWT.SINGLE | SWT.LEFT | SWT.BORDER);
		searchFeatureText.setText(FILTERTEXT);
		searchFeatureText.setMargins(3, 5, 3, 5);
		searchFeatureText.setForeground(shell.getDisplay().getSystemColor(SWT.COLOR_GRAY));
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		searchFeatureText.setLayoutData(gridData);

		final Composite tableComposite = new Composite(featureGroup, SWT.NONE);
		gridData = new GridData(GridData.FILL_HORIZONTAL);
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		tableComposite.setLayoutData(gridData);

		final TableViewer featureTableViewer = new TableViewer(tableComposite, SWT.BORDER | SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL);
		featureTable = featureTableViewer.getTable();
		featureTableViewer.setContentProvider(new ArrayContentProvider());
		final TableViewerColumn viewerNameColumn = new TableViewerColumn(featureTableViewer, SWT.NONE);
		final TableColumnLayout tableColumnLayout = new TableColumnLayout();
		tableComposite.setLayout(tableColumnLayout);
		tableColumnLayout.setColumnData(viewerNameColumn.getColumn(), new ColumnWeightData(100, 100, false));

		featureTableViewer.setComparator(new ViewerComparator() {

			@Override
			public int compare(Viewer viewer, Object feature1, Object feature2) {

				return ((IFeature) feature1).getName().compareToIgnoreCase(((IFeature) feature2).getName());
			}

		});

		viewerNameColumn.setLabelProvider(new CellLabelProvider() {

			@Override
			public void update(ViewerCell cell) {
				cell.setText(((IFeature) cell.getElement()).getName());
				cell.setImage(FEATURE_SYMBOL);
			}
		});

		searchFeatureText.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				if (!FILTERTEXT.equalsIgnoreCase(searchFeatureText.getText())) {
					final ViewerFilter searchFilter = new ViewerFilter() {

						@Override
						public boolean select(Viewer viewer, Object parentElement, Object element) {
							return ((IFeature) element).getName().toLowerCase(Locale.ENGLISH).contains(searchFeatureText.getText().toLowerCase(Locale.ENGLISH));
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
				final TableItem[] selectedItem = featureTable.getSelection();
				String featureName = selectedItem[0].getText();
				if (featureName.matches(".*?\\s+.*")) {
					featureName = "\"" + featureName + "\"";
				} else {
					for (final String op : Operator.NAMES) {
						if (featureName.equalsIgnoreCase(op)) {
							featureName = "\"" + featureName + "\"";
							break;
						}
					}
				}

				constraintText.copyIn(featureName);
			}
		});

	}

	/**
	 * Initializes the upper part of the dialog.
	 */
	private void initHead() {
		headerPanel = new HeaderPanel(shell);
		headerPanel.setHeader(defaultHeaderText);
		headerPanel.setDetails(defaultDetailsText, HeaderPanel.HeaderDescriptionImage.NONE);
	}

	/**
	 * Initializes the shell.
	 */
	private void initShell() {
		shell = new Shell(Display.getCurrent(), SWT.APPLICATION_MODAL | SWT.SHEET);
		shell.setText(DEFAULT_DIALOG_TITLE);
		shell.setImage(FEATURE_SYMBOL);
		shell.setSize(500, 585);

		final GridLayout shellLayout = new GridLayout();
		shellLayout.marginWidth = 0;
		shellLayout.marginHeight = 0;
		shell.setLayout(shellLayout);

		final Monitor primary = shell.getDisplay().getPrimaryMonitor();
		final Rectangle bounds = primary.getBounds();
		final Rectangle rect = shell.getBounds();
		final int x = bounds.x + ((bounds.width - rect.width) / 2);
		final int y = bounds.y + ((bounds.height - rect.height) / 2);
		shell.setLocation(x, y);
		shell.addListener(SWT.Traverse, new Listener() {

			@Override
			public void handleEvent(Event event) {
				if ((event.detail == SWT.TRAVERSE_ESCAPE) && !adapter.isProposalPopupOpen()) {

					cancelButtonPressEvent();

				}
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

	public void setInputText(String text) {
		String constrainText = Operator.isOperatorName(text) || text.contains(" ") ? "\"" + text + "\"" : text;
		constrainText += " ";

		constraintText.setText(constrainText);
		constraintText.setSelection(constrainText.length());
	}

	private void setupContentProposal() {
		try {
			final KeyStroke keyStroke = KeyStroke.getInstance(StringTable.KEYSTROKE_SHORTCUT_FOR_PROPOSAL);

			final char[] autoActivationCharacters = new char[Character.MAX_VALUE];
			for (char c = Character.MIN_VALUE; c < Character.MAX_VALUE; c++) {
				autoActivationCharacters[c] = c;
			}

			adapter = new ContentProposalAdapter(constraintText, new SimpleSyntaxHighlighterConstraintContentAdapter(),
					new ConstraintContentProposalProvider(Functional.toSet(FeatureUtils.extractFeatureNames(featureModel.getFeatures()))), keyStroke,
					autoActivationCharacters);

			adapter.setAutoActivationDelay(PROPOSAL_AUTO_ACTIVATION_DELAY);
			adapter.setPopupSize(new Point(250, 85));

			adapter.setLabelProvider(new ConstraintProposalLabelProvider());

		} catch (final ParseException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Updates the dialogs state, changing the default button and setting the text for this button depending on the current
	 * {@link ConstraintDialog.DialogState}.
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
			okButton.setText(SAVE_ANYWAY);
			break;
		default:
			okButton.setEnabled(false);
			shell.setDefaultButton(cancelButton);
			autoSetOkButtonText();
			break;
		}
	}

	/**
	 * Validates the current constraint in constraintText.
	 *
	 */
	private void validate() {
		headerPanel.setDetails(StringTable.CHECKING_CONSTRAINTS, HeaderPanel.HeaderDescriptionImage.NONE);
		Display.getDefault().syncExec(new Runnable() {

			@Override
			public void run() {
				final String text = constraintText.getText();
				final List<String> featureNamesList = FeatureUtils.getFeatureNamesList(featureModel);
				final NodeReader nodeReader = new NodeReader();
				final boolean wellFormed = nodeReader.isWellFormed(text.trim(), featureNamesList);

				constraintText.underlineEverything(!wellFormed && constraintText.getUnknownWords().isEmpty());

				if (wellFormed) {
					VALIDATOR.validateAsync(constraint, VALIDATION_TIME_OUT, featureModel, text, onCheckStarted, onVoidsModelCheckComplete,
							onFalseOptionalCheckComplete, onDeadFeatureCheckComplete, onIsRedundantCheckComplete, onCheckEnded, onIsTautology,
							onIsNotSatisfiable);
					updateDialogState(DialogState.SAVE_CHANGES_ENABLED);
				} else {
					headerPanel.setDetails(String.format(StringTable.CONSTRAINT_CONNOT_BE_SAVED, nodeReader.getErrorMessage().getMessage()),
							HeaderPanel.HeaderDescriptionImage.ERROR);
					updateDialogState(DialogState.SAVE_CHANGES_DISABLED);
				}
			}
		});
	}
}
