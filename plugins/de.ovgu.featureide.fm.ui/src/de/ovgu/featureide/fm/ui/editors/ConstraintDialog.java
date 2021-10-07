/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.CANCEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_DIALOG;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_NEW_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_PROPOSITIONAL_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.EDIT_PROPOSITIONAL_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.EDIT_YOUR_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.OPERATORS;
import static de.ovgu.featureide.fm.core.localization.StringTable.PLEASE_INSERT_A_CONSTRAINT_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SAVE;
import static de.ovgu.featureide.fm.core.localization.StringTable.SAVE_ANYWAY;
import static de.ovgu.featureide.fm.core.localization.StringTable.TYPE_FILTER_TEXT;
import static de.ovgu.featureide.fm.core.localization.StringTable.UPDATE;
import static de.ovgu.featureide.fm.core.localization.StringTable.YOUR_INPUT_CONSTAINS_SYNTAX_ERRORS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.YOU_CAN_CREATE_OR_EDIT_CONSTRAINTS_WITH_THIS_DIALOG_;

import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.function.Consumer;

import org.eclipse.core.databinding.observable.set.IObservableSet;
import org.eclipse.core.databinding.observable.set.WritableSet;
import org.eclipse.jface.bindings.keys.KeyStroke;
import org.eclipse.jface.bindings.keys.ParseException;
import org.eclipse.jface.databinding.viewers.IViewerUpdater;
import org.eclipse.jface.databinding.viewers.ObservableSetContentProvider;
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
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
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
import org.prop4j.Node;
import org.prop4j.NodeReader;
import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.Operator;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelProperty;
import de.ovgu.featureide.fm.core.io.Problem.Severity;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.ConstraintDialog.HeaderPanel.HeaderDescriptionImage;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.AbstractFeatureModelOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.CreateConstraintOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.EditConstraintOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * A simple editor for propositional constraints written below the feature diagram.
 *
 * @author Christian Becker
 * @author Thomas Thuem
 * @author David Broneske
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 * @author Sebastian Krieter
 */
public class ConstraintDialog implements GUIDefaults {

	/**
	 *
	 */
	private static final String ENTER_A_NEW_OR_EXISTING_TAG_NAME = "enter a new or existing tag name";

	/**
	 * Data class
	 *
	 * @author Marcus Pinnecke
	 */
	public static class ValidationMessage {

		private final String message;
		private final Severity severity;
		private final DialogState saveState;
		private Boolean initialAnalysisSuccess = null;

		public ValidationMessage(String message) {
			this(message, null, null);
		}

		public ValidationMessage(String message, Severity severity) {
			this(message, severity, null);
		}

		public ValidationMessage(String message, DialogState saveState) {
			this(message, null, saveState);
		}

		public ValidationMessage(String message, Severity severity, DialogState saveState) {
			this.message = message;
			this.severity = severity;
			this.saveState = saveState;
		}

		public String getMessage() {
			return message;
		}

		public Severity getSeverity() {
			return severity;
		}

		public DialogState getSaveState() {
			return saveState;
		}

		public Boolean getInitialAnalysisSuccess() {
			return initialAnalysisSuccess;
		}

		public void setInitialAnalysisSuccess(Boolean initialAnalysisSuccess) {
			this.initialAnalysisSuccess = initialAnalysisSuccess;
		}

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
			ERROR, WARNING, INFO, NONE
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
		 * Brief text what's the current mode for the dialog. This is more or less a visualisation of EDITING or "creating" mode of this dialog.
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
		 * {@link #setDetails(String, HeaderDescriptionImage)}).
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
			gridData.heightHint = 70;
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
		 * @param image Image to display
		 */
		public void setDetails(String text, HeaderDescriptionImage image) {
			detailsLabel.setText(text);
			setImage(image);
		}

		/**
		 * Sets the header text for this panel. This text should highlight the current dialogs state, e.g. editing an existing constraint. More information
		 * should be displayed in the details text are.
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
			case INFO:
				headerDescriptionImageLabel.setImage(GUIDefaults.FM_INFO);
				break;
			default:
				headerDescriptionImageLabel.setImage(GUIDefaults.IMAGE_EMPTY);
				break;
			}
			headerDescriptionImageLabel.redraw();

		}
	}

	static class StringTable {

		static final String DEFAULT_DETAILS_NEW_CONSTRAINT = CREATE_PROPOSITIONAL_CONSTRAINT;

		static final String DEFAULT_HEADER_NEW_CONSTRAINT = "Create new Constraint";

		static final String DEFAULT_DETAILS_EDIT_CONSTRAINT = EDIT_PROPOSITIONAL_CONSTRAINT;

		static final String DEFAULT_HEADER_EDIT_CONSTRAINT = EDIT_YOUR_CONSTRAINT;

		static final String VERB_UPDATE = UPDATE;

		static final String VERB_CREATE = CREATE;

		static final String OK_BUTTON_TEXT = "%s Constraint";

		static final String VERB_SAVE = SAVE;

		static final String HREF_HELP_LINK = "http://www.cs.utexas.edu/~schwartz/ATS/fopdocs/guidsl.html";

		static final String PLEASE_INSERT_CONSTRAINT = PLEASE_INSERT_A_CONSTRAINT_;

		static final String KEYSTROKE_SHORTCUT_FOR_PROPOSAL = "Ctrl+Space";

		static final String CONSTRAINT_CONTAINS_SYNTAX_ERRORS = YOUR_INPUT_CONSTAINS_SYNTAX_ERRORS_;

		static final String CONSTRAINT_CONNOT_BE_SAVED = "Constraint is invalid and can not be saved:\n%s";

		static final String CONSTRAINT_IS_NOT_VALIDATED =
			"Constraint is not validated as automated analyses are disabled. Enable automated analyses in the feature diagram editor to activate interactive constraint validation.";

	}

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
	public static enum DialogState {
		SAVE_CHANGES_ENABLED, SAVE_CHANGES_DISABLED, SAVE_CHANGES_DONT_MIND
	}

	/**
	 * Mode in which the dialog runs. Use "UPDATE" if an exiting constraint should be edited and "CREATE" otherwise
	 *
	 * @author Marcus Pinnecke
	 */
	public static enum Mode {
		UPDATE, CREATE
	}

	private static final String FILTERTEXT = TYPE_FILTER_TEXT;

	/**
	 * The dialogs title text.
	 */
	private static final String DEFAULT_DIALOG_TITLE = CONSTRAINT_DIALOG;

	private final static int PROPOSAL_AUTO_ACTIVATION_DELAY = 500;

	/**
	 * Current constraint editing mode.
	 */
	private final Mode mode;

	/**
	 * The panel on the top of this dialog showing useful information and details.
	 */
	private HeaderPanel headerPanel;

	/**
	 * An object which contains several validation functionalities used in this dialog to check if a given constraint text is valid.
	 */
	private ConstraintTextValidator validator;
	private final IFeatureModelManager featureModelManager;
	private final List<String> featureNamesList;

	private Shell shell;

	private String initialConstraint;
	private Group featureGroup;
	private Group descriptionGroup;

	private StyledText searchFeatureText;
	private final SashForm sashForm;
	private Text constraintDescriptionText;

	private Table featureTable;
	private Group buttonGroup;
	private Composite constraintTextComposite;
	private SimpleSyntaxHighlightEditor constraintText;
	private Button okButton;

	private final IConstraint constraint;
	private String defaultDetailsText;

	private String defaultHeaderText;

	private Button cancelButton;

	/**
	 * Content proposal pop up.
	 */
	private ContentProposalAdapter adapter;

	private final Consumer<ValidationMessage> onUpdate = new Consumer<ValidationMessage>() {

		@Override
		public void accept(final ValidationMessage message) {
			Display.getDefault().syncExec(new Runnable() {

				@Override
				public void run() {
					if (message.getSeverity() != null) {
						switch (message.getSeverity()) {
						case ERROR:
							update(message.getMessage(), HeaderPanel.HeaderDescriptionImage.ERROR, message.getSaveState());
							break;
						case INFO:
							update(message.getMessage(), HeaderPanel.HeaderDescriptionImage.INFO, message.getSaveState());
							break;
						case WARNING:
							update(message.getMessage(), HeaderPanel.HeaderDescriptionImage.WARNING, message.getSaveState());
							break;
						default:
							break;
						}
					} else {
						update(message.getMessage(), HeaderPanel.HeaderDescriptionImage.NONE, message.getSaveState());
						if ((message.getInitialAnalysisSuccess() != null) && message.getInitialAnalysisSuccess()) {
							validate();
						}
					}
				}

			});
		}
	};

	/**
	 * <code>tagGroup</code> holds the elements for the constraint tags section.
	 */
	private Group tagGroup;
	/**
	 * <code>tagEntryText</code> contains a text field to enter new tag names.
	 */
	private StyledText tagEntryText;

	/**
	 * Create a new {@link ConstraintDialog} for the feature model managed by <code>featureModelManager</code>. <br> <br> <code>constraint</code> may either be
	 * null, in which case this dialog creates a new constraint, or be an existing constraint the user wants to edit.
	 *
	 * @param featureModelManager - {@link IFeatureModelManager}
	 * @param constraint - {@link IConstraint}
	 */
	public ConstraintDialog(final IFeatureModelManager featureModelManager, final IConstraint constraint) {
		this.featureModelManager = featureModelManager;
		featureNamesList = FeatureUtils.getFeatureNamesList(featureModelManager.getSnapshot());
		this.constraint = constraint;

		final String constraintDescriptionText;
		final Set<String> constraintTags;

		if (constraint == null) {
			constraintDescriptionText = "";
			constraintTags = new HashSet<>();
			defaultDetailsText = StringTable.DEFAULT_DETAILS_NEW_CONSTRAINT;
			defaultHeaderText = StringTable.DEFAULT_HEADER_NEW_CONSTRAINT;
			initialConstraint = "";
			mode = Mode.CREATE;
		} else {
			constraintDescriptionText = constraint.getDescription();
			constraintTags = constraint.getTags();
			defaultDetailsText = StringTable.DEFAULT_DETAILS_EDIT_CONSTRAINT;
			defaultHeaderText = StringTable.DEFAULT_HEADER_EDIT_CONSTRAINT;
			initialConstraint = constraint.getNode().toString(NodeWriter.textualSymbols);
			mode = Mode.UPDATE;
		}

		initShell();
		initHead();

		sashForm = new SashForm(shell, SWT.HORIZONTAL);
		final GridData layoutData = new GridData();
		layoutData.horizontalAlignment = GridData.FILL;
		layoutData.verticalAlignment = GridData.FILL;
		layoutData.grabExcessVerticalSpace = true;
		layoutData.grabExcessHorizontalSpace = true;
		sashForm.setLayoutData(layoutData);

		initFeatureGroup();
		initConstraintDescriptionText(constraintDescriptionText);
		initTagGroup(constraintTags);
		initButtonGroup();
		initConstraintText();
		initBottom();
		constraintText.setFocus();
		constraintText.setSelection(constraintText.getCharCount());

		shell.open();

		update(StringTable.PLEASE_INSERT_CONSTRAINT, HeaderPanel.HeaderDescriptionImage.NONE, DialogState.SAVE_CHANGES_DISABLED);
		// Only use validator when automated constraint analyses are enabled.
		if (FeatureModelProperty.isRunCalculationAutomatically(featureModelManager.getVarObject())
			&& FeatureModelProperty.isCalculateFeatures(featureModelManager.getVarObject())
			&& FeatureModelProperty.isCalculateConstraints(featureModelManager.getVarObject())) {
			validator = new ConstraintTextValidator();
			validator.init(featureModelManager.getVariableFormula(), constraint, onUpdate);
		}

		if (constraint != null) {
			validate();
		}
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
		if (validator != null) {
			validator.cancelValidation();
		}
		shell.dispose();
	}

	/**
	 * Closes the shell and adds new constraint to the feature model respectively updates the existing constraint, if possible.
	 */
	private void closeShell() {
		final String input = constraintText.getText().trim();
		final NodeReader nodeReader = new NodeReader();
		nodeReader.setFeatureNames(featureNamesList);
		final Node propNode = nodeReader.stringToNode(input);
		final String constraintDescription = constraintDescriptionText.getText().trim();

		final AbstractFeatureModelOperation op =
			(constraint != null) ? new EditConstraintOperation(featureModelManager, constraint, propNode, constraintDescription)
				: new CreateConstraintOperation(propNode, featureModelManager, constraintDescription);

		FeatureModelOperationWrapper.run(op);

		shell.dispose();
	}

	/**
	 * Creates a {@link StyledText} field that displays <code>defaultText</code> when unselected for the given <code>parent</code> composite.
	 *
	 * @param defaultText - {@link String}
	 * @param parent - {@link Composite}
	 * @return new {@link StyledText}
	 */
	private StyledText createTextField(String defaultText, Composite parent) {
		final StyledText text = new StyledText(parent, SWT.SINGLE | SWT.LEFT | SWT.BORDER);
		text.setText(defaultText);
		text.setMargins(3, 5, 3, 5);
		text.setForeground(sashForm.getDisplay().getSystemColor(SWT.COLOR_GRAY));
		text.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		text.addListener(SWT.FocusOut, new Listener() {

			@Override
			public void handleEvent(Event event) {
				if (text.getText().isEmpty()) {
					text.setText(defaultText);
					text.setForeground(sashForm.getDisplay().getSystemColor(SWT.COLOR_GRAY));

				}

			}
		});
		text.addListener(SWT.FocusIn, new Listener() {

			@Override
			public void handleEvent(Event event) {
				if (defaultText.equals(text.getText())) {
					text.setText("");
				}
				text.setForeground(sashForm.getDisplay().getSystemColor(SWT.COLOR_BLACK));
			}

		});
		return text;
	}

	/**
	 * Initializes the bottom part of the dialog
	 */
	private void initBottom() {
		final GridData gridData = new GridData(GridData.FILL_HORIZONTAL);

		final Composite lastComposite = new Composite(shell, SWT.NONE);
		lastComposite.setLayoutData(gridData);

		final FormLayout lastCompositeLayout = new FormLayout();
		lastCompositeLayout.marginHeight = 5;
		lastCompositeLayout.marginTop = 5;
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
		formDataOk.width = 130;
		formDataOk.right = new FormAttachment(cancelButton, -5);
		formDataOk.bottom = new FormAttachment(100, -5);
		okButton.setLayoutData(formDataOk);

		cancelButton.setLayoutData(formDataCancel);

		shell.setTabList(new Control[] { sashForm, buttonGroup, constraintTextComposite, lastComposite });

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
		constraintText.setLayoutData(formDataConstraintText);
		constraintText.setText(initialConstraint);
		constraintText.setMargins(10, 5, 3, 5);

		constraintText.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				validate();
			}
		});

	}

	/**
	 * Updates the dialogs state, displaying the given message, changing the default button, and setting the text for this button depending on the current
	 * {@link ConstraintDialog.DialogState}.
	 *
	 * @param message The message to display
	 * @param image The image to display
	 * @param saveState The state to consider
	 */
	private void update(String message, HeaderDescriptionImage image, DialogState saveState) {
		if (shell.isDisposed()) {
			return;
		}
		if (message != null) {
			headerPanel.setDetails(message, image);
		}
		if (saveState != null) {
			switch (saveState) {
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
	}

	/**
	 * Initializes the text field containing the description.
	 *
	 * @param description - {@link String}
	 */
	private void initConstraintDescriptionText(String description) {

		descriptionGroup = new Group(sashForm, SWT.NONE);
		descriptionGroup.setText("Description");
		final GridData gridData = new GridData(GridData.FILL_BOTH);
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		descriptionGroup.setLayoutData(gridData);
		final GridLayout featureGroupLayout = new GridLayout();
		featureGroupLayout.numColumns = 1;
		descriptionGroup.setLayout(featureGroupLayout);
		constraintDescriptionText = new Text(descriptionGroup, SWT.MULTI | SWT.BORDER | SWT.WRAP | SWT.V_SCROLL);
		constraintDescriptionText.setLayoutData(gridData);
		constraintDescriptionText.setText(description);

	}

	/**
	 * Initializes the group containing the tags.
	 *
	 * @param tags - {@link Set}
	 */
	private void initTagGroup(Set<String> tags) {
		// Create the tag group, and configure its layout.
		tagGroup = new Group(sashForm, SWT.NONE);
		tagGroup.setText("Tags");
		tagGroup.setLayoutData(new GridData(GridData.FILL, GridData.FILL, true, true));
		final GridLayout tagGroupLayout = new GridLayout(2, false);
		tagGroup.setLayout(tagGroupLayout);

		// Configure tagEntryText.
		tagEntryText = createTextField(ENTER_A_NEW_OR_EXISTING_TAG_NAME, tagGroup);

		// Also create a drop-down menu for tags as there already exists for features.

		// Give an overview of the constraint's current tags in <code>tags</code>.
		final Composite tableComposite = new Composite(tagGroup, SWT.NONE);
		tableComposite.setLayoutData(new GridData(GridData.FILL, GridData.FILL, true, true));

		final TableViewer tagTableViewer = new TableViewer(tableComposite, SWT.BORDER | SWT.SINGLE | SWT.H_SCROLL | SWT.V_SCROLL);
		final Table tagTable = tagTableViewer.getTable();
		final ObservableSetContentProvider<String> provider = new ObservableSetContentProvider<>(new IViewerUpdater<String>() {

			@Override
			public void insert(String element, int position) {}

			@Override
			public void remove(String element, int position) {}

			@Override
			public void replace(String oldElement, String newElement, int position) {}

			@Override
			public void move(String element, int oldPosition, int newPosition) {}

			@Override
			public void add(String[] elements) {}

			@Override
			public void remove(String[] elements) {}
		});

		tagTableViewer.setContentProvider(provider);
		final IObservableSet<String> observableTags = new WritableSet<>(tags, String.class);
		tagTableViewer.setInput(observableTags);

		// Add an button that allows the addition of existing tags.
		final Button addTagButton = new Button(tagGroup, SWT.NONE);
		addTagButton.setText("Add Tag");
		// When pressing addTagButton, add the new tag to tags.
		addTagButton.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent event) {
				final String newTagText = tagEntryText.getText();
				if (!newTagText.isEmpty() && !newTagText.equals(ENTER_A_NEW_OR_EXISTING_TAG_NAME)) {
					final IObservableSet<String> newTagSet = new WritableSet<>(observableTags, String.class);
					newTagSet.add(newTagText);
					provider.inputChanged(tagTableViewer, observableTags, newTagSet);
					observableTags.add(newTagText);
					tagEntryText.setText(ENTER_A_NEW_OR_EXISTING_TAG_NAME);
				}
			}
		});
	}

	/**
	 * Initializes the group containing the searchText and featureTable.
	 */
	private void initFeatureGroup() {
		featureGroup = new Group(sashForm, SWT.NONE);
		featureGroup.setText("Features");
		GridData gridData = new GridData(GridData.FILL);
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		featureGroup.setLayoutData(gridData);
		final GridLayout featureGroupLayout = new GridLayout();

		featureGroupLayout.numColumns = 1;

		featureGroup.setLayout(featureGroupLayout);

		searchFeatureText = createTextField(FILTERTEXT, featureGroup);

		final Composite tableComposite = new Composite(featureGroup, SWT.NONE);
		gridData = new GridData(SWT.FILL, 200, true, true);
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
				return ((String) feature1).compareToIgnoreCase(((String) feature2));
			}

		});

		viewerNameColumn.setLabelProvider(new CellLabelProvider() {

			@Override
			public void update(ViewerCell cell) {
				cell.setText((String) cell.getElement());
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
							return ((String) element).toLowerCase(Locale.ENGLISH).contains(searchFeatureText.getText().toLowerCase(Locale.ENGLISH));
						}

					};
					featureTableViewer.addFilter(searchFilter);

				}
			}

		});

		featureTableViewer.setInput(featureNamesList);

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
		shell.setMinimumSize(280, 575);

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
			if (validator != null) {
				validator.cancelValidation();
			}
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
					new ConstraintContentProposalProvider(featureNamesList), keyStroke, autoActivationCharacters);

			adapter.setAutoActivationDelay(PROPOSAL_AUTO_ACTIVATION_DELAY);
			adapter.setPopupSize(new Point(250, 85));

			adapter.setLabelProvider(new ConstraintProposalLabelProvider());

		} catch (final ParseException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	/**
	 * Validates the current constraint in constraintText.
	 */
	private void validate() {
		final String text = constraintText.getText().trim();
		if (text.isEmpty()) {
			update(StringTable.PLEASE_INSERT_CONSTRAINT, HeaderPanel.HeaderDescriptionImage.NONE, DialogState.SAVE_CHANGES_DISABLED);
		} else {
			final NodeReader nodeReader = new NodeReader();
			nodeReader.setFeatureNames(featureNamesList);
			final Node constraintNode = nodeReader.stringToNode(text);
			if (constraintNode == null) {
				update(String.format(StringTable.CONSTRAINT_CONNOT_BE_SAVED, nodeReader.getErrorMessage().getMessage()),
						HeaderPanel.HeaderDescriptionImage.ERROR, DialogState.SAVE_CHANGES_DISABLED);
			} else {
				if (validator != null) {
					if (!validator.validateAsync(constraintNode, onUpdate)) {
						update(null, null, DialogState.SAVE_CHANGES_DONT_MIND);
					}
				} else {
					// Show the user that constraints are not checked for validity as automated analyses are disabled
					update(StringTable.CONSTRAINT_IS_NOT_VALIDATED, HeaderPanel.HeaderDescriptionImage.WARNING, DialogState.SAVE_CHANGES_DONT_MIND);
				}
			}
			constraintText.updateHighlight(nodeReader.errorType);
		}
	}
}
