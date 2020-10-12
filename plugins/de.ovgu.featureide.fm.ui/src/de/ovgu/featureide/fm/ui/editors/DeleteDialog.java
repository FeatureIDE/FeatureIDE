package de.ovgu.featureide.fm.ui.editors;

import java.util.List;

import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.layout.GridDataFactory;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.program.Program;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Link;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * A MessageDialog for when a feature can not be deleted regularly.
 *
 * The dialog shows reasons for why the feature could not be deleted regularly. There can be different delete options.
 *
 * @author Soeren Viegener
 * @author Philipp Vulpius
 */
public class DeleteDialog extends MessageDialog {

	/**
	 * Constructor
	 *
	 * @param parentShell
	 * @param multiple <code>true</code> if multiple features are being deleted, <code>false</code> if not
	 * @param dialogReasons A List of Strings with reasons for the dialog
	 * @param dialogButtonLabels A String array with labels for the buttons of the dialog
	 * @param defaultIndex The index of the button being selected by default
	 */
	public DeleteDialog(Shell parentShell, boolean multiple, List<String> dialogReasons, String[] dialogButtonLabels, int defaultIndex) {
		super(parentShell, StringTable.DELETE_WARNING, GUIDefaults.FEATURE_SYMBOL, null, MessageDialog.WARNING, dialogButtonLabels, defaultIndex);
		message = getSlicingDialogMessage(multiple, dialogReasons);
	}

	/**
	 * Creates the content of the dialog by adding an image and a text
	 *
	 * The text contains the reasons for this dialog and a link to the wiki for further information
	 *
	 * @param composite
	 * @return
	 */
	@Override
	protected Control createMessageArea(final Composite composite) {
		final Image image = getImage();
		if (image != null) {
			imageLabel = new Label(composite, SWT.NULL);
			image.setBackground(imageLabel.getBackground());
			imageLabel.setImage(image);
			GridDataFactory.fillDefaults().align(SWT.CENTER, SWT.BEGINNING).applyTo(imageLabel);
		}
		if (message != null) {
			final Link link = new Link(composite, getMessageLabelStyle());
			link.setText(message);
			link.addSelectionListener(new SelectionAdapter() {

				@Override
				public void widgetSelected(SelectionEvent e) {
					Program.launch(StringTable.WIKI_DELETING_URL);
				}
			});
			GridDataFactory.fillDefaults().align(SWT.FILL, SWT.BEGINNING).grab(true, false)
					.hint(convertHorizontalDLUsToPixels(IDialogConstants.MINIMUM_MESSAGE_AREA_WIDTH), SWT.DEFAULT).applyTo(link);
		}
		return composite;
	}

	/**
	 * Gets the message for the dialog
	 *
	 * The text contains the reasons for this dialog and a link to the wiki for further information.
	 *
	 * @param multiple <code>true</code> if multiple features are being deleted, <code>false</code> if not
	 * @param dialogReasons A List of Strings with reasons for the dialog
	 * @return The message for the dialog containing reasons and a link to the wiki
	 */
	private String getSlicingDialogMessage(boolean multiple, List<String> dialogReasons) {
		String message = "";
		if (multiple) {
			message += StringTable.DELETING_THESE_FEATURES_MAY_RESULT_IN_UNWANTED_CHANGES_AS;
		} else {
			message += StringTable.DELETING_THIS_FEATURE_MAY_RESULT_IN_UNWANTED_CHANGES_AS;
		}
		message += "\n";

		// add bullet dashes to the reasons for better layout
		for (int i = 0; i < dialogReasons.size(); i++) {
			dialogReasons.set(i, StringTable.LIST_BULLET_DASH + dialogReasons.get(i));
		}

		message += String.join("\n", dialogReasons);

		message +=
			"\n\n" + StringTable.FOR_MORE_INFORMATION_PLEASE_VISIT_THE + " <a href=\"" + StringTable.WIKI_DELETING_URL + "\">" + StringTable.WIKI + "</a>.";
		return message;
	}
}
