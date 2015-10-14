/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.refactoring.pullUp;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.internal.corext.refactoring.structure.IMemberActionInfo;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jdt.internal.ui.IJavaHelpContextIds;
import org.eclipse.jdt.internal.ui.refactoring.RefactoringMessages;
import org.eclipse.jdt.internal.ui.util.ExceptionHandler;
import org.eclipse.jdt.internal.ui.util.SWTUtil;
import org.eclipse.jdt.internal.ui.util.TableLayoutComposite;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TableLayout;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.ui.refactoring.UserInputWizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;
import de.ovgu.featureide.ui.views.outline.ContextOutlineLabelProvider;

/**
 * Wizard page for pull up refactoring wizards which allows to specify the
 * actions on the members to pull up.
 * 
 * @since 3.2
 */
@SuppressWarnings("restriction")
public class PullUpMemberPage extends UserInputWizardPage {

	private class MemberActionInfo implements IMemberActionInfo {

		private static final int NO_ACTION = 2;

		private int action;

		private final AbstractSignature signature;

		public MemberActionInfo(final AbstractSignature signature, final int action) {
			this.signature = signature;
			this.action = action;
		}

		public int getAction() {
			return action;
		}

		public String getActionLabel() {
			return getPullUpActionLabel();
		}

		public AbstractSignature getSignature() {
			return signature;
		}

		public boolean isActive() {
			return getAction() != NO_ACTION;
		}

		public void setAction(int pullUpAction) {
			this.action = pullUpAction;
		}
	}

	private static class MemberActionInfoLabelProvider extends LabelProvider implements ITableLabelProvider {

		private final ILabelProvider fLabelProvider = new ContextOutlineLabelProvider();

		@Override
		public void dispose() {
			super.dispose();
			fLabelProvider.dispose();
		}

		public Image getColumnImage(final Object element, final int columnIndex) {
			final MemberActionInfo info = (MemberActionInfo) element;
			switch (columnIndex) {
			case MEMBER_COLUMN:
				return fLabelProvider.getImage(info.getSignature());
			case ACTION_COLUMN:
				return null;
			default:
				Assert.isTrue(false);
				return null;
			}
		}

		public String getColumnText(final Object element, final int columnIndex) {
			final MemberActionInfo info = (MemberActionInfo) element;
			switch (columnIndex) {
			case MEMBER_COLUMN:
				return fLabelProvider.getText(info.getSignature());
			case ACTION_COLUMN:
				return info.getActionLabel();
			default:
				Assert.isTrue(false);
				return null;
			}
		}
	}

	private static final int ACTION_COLUMN = 1;

	private static final int MEMBER_COLUMN = 0;

	protected static final int PULL_UP_ACTION = 0;

	private static void putToStringMapping(final Map<String, Integer> result, final String[] actionLabels, final int actionIndex) {
		result.put(actionLabels[actionIndex], new Integer(actionIndex));
	}

	protected AbstractClassSignature[] fCandidateTypes = {};

	private Button fDeselectAllButton;

	private Button fSelectAllButton;

	private Label fStatusLine;

	private Label fLabel;

	protected final PullUpMethodPage fSuccessorPage;

	private Combo fSuperTypesCombo;

	private CheckboxTableViewer fTableViewer;

	protected final String[] METHOD_LABELS;

	protected final String[] TYPE_LABELS;

	private final PullUpRefactoring refactoring;

	public PullUpMemberPage(final String name, final PullUpMethodPage page, PullUpRefactoring refactoring) {
		super(name);
		fSuccessorPage = page;
		this.refactoring = refactoring;
		setDescription(RefactoringMessages.PullUpInputPage1_page_message);
		METHOD_LABELS = new String[1];
		METHOD_LABELS[PULL_UP_ACTION] = RefactoringMessages.PullUpInputPage1_pull_up;

		TYPE_LABELS = new String[1];
		TYPE_LABELS[PULL_UP_ACTION] = RefactoringMessages.PullUpInputPage1_pull_up;
	}

	public PullUpRefactoring getPullUpMethodRefactoring() {
		return refactoring;
	}

	private boolean areAllMembersMarkedAsPullUp() {
		return getMembersForAction(PULL_UP_ACTION).length == getTableInput().length;
	}

	protected boolean areAllMembersMarkedAsWithNoAction() {
		return getMembersForAction(MemberActionInfo.NO_ACTION).length == getTableInput().length;
	}

	private MemberActionInfo[] asMemberActionInfos() {
		final List<FujiMethodSignature> toPullUp = Arrays.asList(refactoring.getPullableElements());
		final MemberActionInfo[] result = new MemberActionInfo[toPullUp.size()];
		for (int i = 0; i < toPullUp.size(); i++) {
			result[i] = new MemberActionInfo(toPullUp.get(i), PULL_UP_ACTION);
		}
		return result;
	}

	@Override
	public boolean canFlipToNextPage() {
		return isPageComplete();
	}

	protected void checkPageCompletionStatus(final boolean displayErrors) {
		if (areAllMembersMarkedAsWithNoAction()) {
			if (displayErrors)
				setErrorMessage(getNoMembersMessage());
			setPageComplete(false);
		} else {
			setErrorMessage(null);
			setPageComplete(true);
		}
		fSuccessorPage.fireSettingsChanged();
	}

	private void checkPullUp(final AbstractSignature[] elements, final boolean displayErrors) {
		setActionForMembers(elements, PULL_UP_ACTION);
		updateWizardPage(null, displayErrors);
	}

	private void createButtonComposite(final Composite parent) {
		final Composite composite = new Composite(parent, SWT.NONE);
		composite.setLayoutData(new GridData(GridData.FILL_VERTICAL));
		final GridLayout gl = new GridLayout();
		gl.marginHeight = 0;
		gl.marginWidth = 0;
		composite.setLayout(gl);

		fSelectAllButton = new Button(composite, SWT.PUSH);
		fSelectAllButton.setText(RefactoringMessages.PullUpWizard_select_all_label);
		fSelectAllButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		fSelectAllButton.setEnabled(true);
		SWTUtil.setButtonDimensionHint(fSelectAllButton);
		fSelectAllButton.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(final SelectionEvent event) {
				final AbstractSignature[] members = getMembers();
				setActionForMembers(members, PULL_UP_ACTION);
				updateWizardPage(null, true);
			}
		});

		fDeselectAllButton = new Button(composite, SWT.PUSH);
		fDeselectAllButton.setText(RefactoringMessages.PullUpWizard_deselect_all_label);
		fDeselectAllButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		fDeselectAllButton.setEnabled(false);
		SWTUtil.setButtonDimensionHint(fDeselectAllButton);
		fDeselectAllButton.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(final SelectionEvent event) {
				final AbstractSignature[] members = getMembers();
				setActionForMembers(members, MemberActionInfo.NO_ACTION);
				updateWizardPage(null, true);
			}
		});
	}

	public void createControl(final Composite parent) {
		final Composite composite = new Composite(parent, SWT.NONE);
		final GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		composite.setLayout(layout);

		createSuperTypeControl(composite);
		createSpacer(composite);
		createMemberTableLabel(composite);
		createMemberTableComposite(composite);
		createStatusLine(composite);

		setControl(composite);
		Dialog.applyDialogFont(composite);
		initializeEnablement();
		PlatformUI.getWorkbench().getHelpSystem().setHelp(getControl(), IJavaHelpContextIds.PULL_UP_WIZARD_PAGE);
	}

	private void createMemberTable(final Composite parent) {
		final TableLayoutComposite layouter = new TableLayoutComposite(parent, SWT.NONE);
		layouter.addColumnData(new ColumnWeightData(60, true));
		layouter.addColumnData(new ColumnWeightData(40, true));

		final Table table = new Table(layouter, SWT.H_SCROLL | SWT.V_SCROLL | SWT.MULTI | SWT.BORDER | SWT.FULL_SELECTION | SWT.CHECK);
		table.setHeaderVisible(true);
		table.setLinesVisible(true);

		final GridData gd = new GridData(GridData.FILL_BOTH);
		gd.heightHint = SWTUtil.getTableHeightHint(table, getTableRowCount());
		gd.widthHint = convertWidthInCharsToPixels(30);
		layouter.setLayoutData(gd);

		final TableLayout tableLayout = new TableLayout();
		table.setLayout(tableLayout);

		final TableColumn column0 = new TableColumn(table, SWT.NONE);
		column0.setText(RefactoringMessages.PullUpInputPage1_Member);

		final TableColumn column1 = new TableColumn(table, SWT.NONE);
		column1.setText(RefactoringMessages.PullUpInputPage1_Action);

		fTableViewer = new PullPushCheckboxTableViewer(table);
		fTableViewer.setUseHashlookup(true);
		fTableViewer.setContentProvider(new ArrayContentProvider());
		fTableViewer.setLabelProvider(new MemberActionInfoLabelProvider());
		fTableViewer.addSelectionChangedListener(new ISelectionChangedListener() {

			public void selectionChanged(final SelectionChangedEvent event) {
				updateButtonEnablement(event.getSelection());
			}
		});
		fTableViewer.addCheckStateListener(new ICheckStateListener() {

			public void checkStateChanged(final CheckStateChangedEvent event) {
				final boolean checked = event.getChecked();
				final MemberActionInfo info = (MemberActionInfo) event.getElement();
				if (checked)
					info.setAction(PULL_UP_ACTION);
				else
					info.setAction(MemberActionInfo.NO_ACTION);
				updateWizardPage(null, true);
			}
		});
		fTableViewer.addDoubleClickListener(new IDoubleClickListener() {

			public void doubleClick(final DoubleClickEvent event) {
				editSelectedMembers();
			}
		});

		setTableInput();
		checkPullUp(refactoring.getPullableElements(), false);
		//		setupCellEditors(table);
	}

	protected void createMemberTableComposite(final Composite parent) {
		final Composite composite = new Composite(parent, SWT.NONE);
		final GridData data = new GridData(GridData.FILL_BOTH);
		data.horizontalSpan = 2;
		composite.setLayoutData(data);
		final GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		layout.marginWidth = 0;
		layout.marginHeight = 0;
		composite.setLayout(layout);

		createMemberTable(composite);
		createButtonComposite(composite);
	}

	protected void createMemberTableLabel(final Composite parent) {
		fLabel = new Label(parent, SWT.NONE);
		fLabel.setText(RefactoringMessages.PullUpInputPage1_Specify_actions);
		final GridData data = new GridData();
		data.horizontalSpan = 2;
		fLabel.setLayoutData(data);
	}

	protected void createSpacer(final Composite parent) {
		final Label label = new Label(parent, SWT.NONE);
		final GridData data = new GridData();
		data.horizontalSpan = 2;
		data.heightHint = convertHeightInCharsToPixels(1) / 2;
		label.setLayoutData(data);
	}

	protected void createStatusLine(final Composite composite) {
		fStatusLine = new Label(composite, SWT.NONE);
		final GridData data = new GridData(SWT.FILL, SWT.CENTER, false, false);
		data.horizontalSpan = 2;
		updateStatusLine();
		fStatusLine.setLayoutData(data);
	}

	// String -> Integer
	private Map<String, Integer> createStringMappingForSelectedMembers() {
		final Map<String, Integer> result = new HashMap<String, Integer>();
		putToStringMapping(result, METHOD_LABELS, PULL_UP_ACTION);
		return result;
	}

	private void createSuperTypeCombo(Composite parent) {
		final Label label = new Label(parent, SWT.NONE);
		label.setText(RefactoringMessages.PullUpInputPage1_Select_destination);
		label.setLayoutData(new GridData());

		fSuperTypesCombo = new Combo(parent, SWT.READ_ONLY);
		SWTUtil.setDefaultVisibleItemCount(fSuperTypesCombo);
		if (fCandidateTypes.length > 0) {
			for (int i = 0; i < fCandidateTypes.length; i++) {
				final String comboLabel = fCandidateTypes[i].getName();
				fSuperTypesCombo.add(comboLabel);
			}
			fSuperTypesCombo.select(fCandidateTypes.length - 1);
			fSuperTypesCombo.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		}
	}

	protected void createSuperTypeControl(final Composite parent) {
		try {
			PlatformUI.getWorkbench().getActiveWorkbenchWindow().run(true, false, new IRunnableWithProgress() {
				public void run(final IProgressMonitor monitor) throws InvocationTargetException {
					fCandidateTypes = refactoring.getCandidateTypes(new RefactoringStatus());
				}
			});
			createSuperTypeCombo(parent);
		} catch (InvocationTargetException exception) {
			ExceptionHandler.handle(exception, getShell(), RefactoringMessages.PullUpInputPage_pull_Up, RefactoringMessages.PullUpInputPage_exception);
		} catch (InterruptedException exception) {
			Assert.isTrue(false);
		}
	}

	@Override
	public void dispose() {
		fTableViewer = null;
		super.dispose();
	}

	private void editSelectedMembers() {
		final ISelection preserved = fTableViewer.getSelection();
		try {
			MemberActionInfo[] selectedMembers = getSelectedMembers();
			final String shellTitle = RefactoringMessages.PullUpInputPage1_Edit_members;
			final String labelText = selectedMembers.length == 1 ? Messages.format(RefactoringMessages.PullUpInputPage1_Mark_selected_members_singular,
					(new MemberActionInfoLabelProvider()).getColumnText(selectedMembers[0], MEMBER_COLUMN)) : Messages.format(
					RefactoringMessages.PullUpInputPage1_Mark_selected_members_plural, String.valueOf(selectedMembers.length));
			final Map<String, Integer> stringMapping = createStringMappingForSelectedMembers();
			final String[] keys = stringMapping.keySet().toArray(new String[stringMapping.keySet().size()]);
			Arrays.sort(keys);
			final int initialSelectionIndex = getInitialSelectionIndexForEditDialog(stringMapping, keys);
			final ComboSelectionDialog dialog = new ComboSelectionDialog(getShell(), shellTitle, labelText, keys, initialSelectionIndex);
			dialog.setBlockOnOpen(true);
			if (dialog.open() == Window.CANCEL)
				return;
		} finally {
			updateWizardPage(preserved, true);
		}
	}

	private MemberActionInfo[] getActiveInfos() {
		final MemberActionInfo[] infos = getTableInput();
		final List<MemberActionInfo> result = new ArrayList<MemberActionInfo>(infos.length);
		for (int i = 0; i < infos.length; i++) {
			final MemberActionInfo info = infos[i];
			if (info.isActive())
				result.add(info);
		}
		return result.toArray(new MemberActionInfo[result.size()]);
	}

	private int getCommonActionCodeForSelectedInfos() {
		final MemberActionInfo[] infos = getSelectedMembers();
		if (infos.length == 0)
			return -1;

		final int code = infos[0].getAction();
		for (int i = 0; i < infos.length; i++) {
			if (code != infos[i].getAction())
				return -1;
		}
		return code;
	}

	public AbstractClassSignature getDestinationType() {
		final int index = fSuperTypesCombo.getSelectionIndex();
		if (index >= 0)
			return fCandidateTypes[index];
		return null;
	}

	private int getInitialSelectionIndexForEditDialog(final Map<String, Integer> stringMapping, final String[] keys) {
		final int commonActionCode = getCommonActionCodeForSelectedInfos();
		if (commonActionCode == -1)
			return 0;
		for (final Iterator<String> iter = stringMapping.keySet().iterator(); iter.hasNext();) {
			final String key = iter.next();
			final int action = stringMapping.get(key).intValue();
			if (commonActionCode == action) {
				for (int i = 0; i < keys.length; i++) {
					if (key.equals(keys[i]))
						return i;
				}
				Assert.isTrue(false);
			}
		}
		return 0;
	}

	private AbstractSignature[] getMembers() {
		final MemberActionInfo[] infos = getTableInput();
		final List<AbstractSignature> result = new ArrayList<AbstractSignature>(infos.length);
		for (int index = 0; index < infos.length; index++) {
			result.add(infos[index].getSignature());
		}
		return result.toArray(new AbstractSignature[result.size()]);
	}

	private AbstractSignature[] getMembersForAction(final int action) {
		List<AbstractSignature> result = new ArrayList<AbstractSignature>();
		getMembersForAction(action, false, result);
		return result.toArray(new AbstractSignature[result.size()]);
	}

	private AbstractSignature[] getMethodsForAction(final int action) {
		List<AbstractSignature> result = new ArrayList<AbstractSignature>();
		getMembersForAction(action, true, result);
		return result.toArray(new AbstractSignature[result.size()]);
	}

	private void getMembersForAction(int action, boolean onlyMethods, List<AbstractSignature> result) {
		final MemberActionInfo[] infos = getTableInput();
		for (int index = 0; index < infos.length; index++) {
			MemberActionInfo info = infos[index];
			if (info.getAction() == action)
				result.add(info.getSignature());
		}
	}

	@Override
	public IWizardPage getNextPage() {
		initializeRefactoring();
		if (getMethodsForAction(PULL_UP_ACTION).length == 0)
			return computeSuccessorPage();
		return super.getNextPage();
	}

	protected String getNoMembersMessage() {
		return RefactoringMessages.PullUpInputPage1_Select_members_to_pull_up;
	}

	protected String getPullUpActionLabel() {
		return RefactoringMessages.PullUpInputPage1_pull_up;
	}

	protected String getReplaceButtonLabel() {
		return RefactoringMessages.PullUpInputPage1_label_use_destination;
	}

	private MemberActionInfo[] getSelectedMembers() {
		Assert.isTrue(fTableViewer.getSelection() instanceof IStructuredSelection);
		final IStructuredSelection structured = (IStructuredSelection) fTableViewer.getSelection();
		final List<?> result = structured.toList();
		return result.toArray(new MemberActionInfo[result.size()]);
	}

	private MemberActionInfo[] getTableInput() {
		return (MemberActionInfo[]) fTableViewer.getInput();
	}

	protected int getTableRowCount() {
		return 10;
	}

	protected void initializeEnablement() {
		MemberActionInfo[] infos = asMemberActionInfos();
		final boolean enabled = infos.length > 0;
		fTableViewer.getTable().setEnabled(enabled);
		fStatusLine.setEnabled(enabled);
		fLabel.setEnabled(enabled);
	}

	private void initializeRefactoring() {
		refactoring.setPullUpSignatures(getMembersForAction(PULL_UP_ACTION));
		final AbstractClassSignature destination = getDestinationType();
		if (destination != null)
			refactoring.setDestinationType(destination);
	}

	@Override
	protected boolean performFinish() {
		initializeRefactoring();
		return super.performFinish();
	}

	private void setActionForMembers(final AbstractSignature[] members, final int action) {
		final MemberActionInfo[] infos = getTableInput();
		for (int i = 0; i < members.length; i++) {
			for (int j = 0; j < infos.length; j++) {
				if (infos[j].getSignature().equals(members[i]))
					infos[j].setAction(action);
			}
		}
	}

	private void setTableInput() {
		fTableViewer.setInput(asMemberActionInfos());
	}

	@Override
	public void setVisible(final boolean visible) {
		super.setVisible(visible);
		if (visible) {
			try {
				//refactoring.resetEnvironment();
			} finally {
				fTableViewer.setSelection(new StructuredSelection(getActiveInfos()), true);
				fTableViewer.getControl().setFocus();
			}
		}
	}

	private void updateButtonEnablement(final ISelection selection) {
		if (fSelectAllButton != null)
			fSelectAllButton.setEnabled(!areAllMembersMarkedAsPullUp());
		if (fDeselectAllButton != null)
			fDeselectAllButton.setEnabled(!areAllMembersMarkedAsWithNoAction());
	}

	private void updateStatusLine() {
		if (fStatusLine == null)
			return;
		Object[] selectedMembers = fTableViewer.getCheckedElements();
		final int selected = selectedMembers.length;
		final String msg = selected == 1 ? Messages.format(RefactoringMessages.PullUpInputPage1_status_line_singular,
				(new MemberActionInfoLabelProvider()).getColumnText(selectedMembers[0], MEMBER_COLUMN)) : Messages.format(
				RefactoringMessages.PullUpInputPage1_status_line_plural, String.valueOf(selected));
		fStatusLine.setText(msg);
	}

	private void updateWizardPage(final ISelection selection, final boolean displayErrors) {
		fTableViewer.refresh();
		if (selection != null) {
			fTableViewer.getControl().setFocus();
			fTableViewer.setSelection(selection);
		}
		checkPageCompletionStatus(displayErrors);
		updateButtonEnablement(fTableViewer.getSelection());
		updateStatusLine();
	}
}
