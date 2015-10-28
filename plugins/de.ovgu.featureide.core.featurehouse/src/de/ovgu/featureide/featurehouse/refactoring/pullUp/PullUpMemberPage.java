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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jdt.internal.ui.IJavaHelpContextIds;
import org.eclipse.jdt.internal.ui.refactoring.RefactoringMessages;
import org.eclipse.jdt.internal.ui.util.ExceptionHandler;
import org.eclipse.jdt.internal.ui.util.SWTUtil;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.Viewer;
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
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.ContainerCheckedTreeViewer;

import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.fm.core.Feature;

/**
 * Wizard page for pull up refactoring wizards which allows to specify the
 * actions on the members to pull up.
 * 
 * @since 3.2
 */
@SuppressWarnings("restriction")
public class PullUpMemberPage extends UserInputWizardPage {
	
	private static class PullUpHierarchyContentProvider implements ITreeContentProvider {

		private final Map<AbstractSignature, List<Feature>> clonedSignatures;
		
		public void dispose() {
		}
		
		public PullUpHierarchyContentProvider(Map<AbstractSignature, List<Feature>> clonedSignatures){
			this.clonedSignatures = clonedSignatures;
		}

		public Object[] getChildren(final Object parentElement) {
			
			Set<Object> elements = new HashSet<>();
			if (parentElement instanceof ExtendedPullUpSignature) {
				final AbstractSignature signature = ((ExtendedPullUpSignature) parentElement).getSignature();
				if (clonedSignatures.containsKey(signature))
					elements.addAll(clonedSignatures.get(signature));
			}
			return elements.toArray();
		}

		public Object[] getElements(final Object inputElement) {
			return ((Set<?>) inputElement).toArray();
		}

		public Object getParent(final Object element) {
//			if (element instanceof Feature)
//				return ((ExtendedPullUpSignature) element).getParent();
				
			return null;
		}
		
		public boolean hasChildren(final Object element) {
			return getChildren(element).length > 0;
		}
		
		public void inputChanged(final Viewer viewer, final Object oldInput, final Object newInput) {
		}
	}
	
	private static class PullUpMemberLabelProvider extends LabelProvider implements ITableLabelProvider {

		private final ILabelProvider fLabelProvider= new PullUpHierarchyLabelProvider();

		@Override
		public void dispose() {
			super.dispose();
			fLabelProvider.dispose();
		}

		public Image getColumnImage(final Object element, final int columnIndex) {
			switch (columnIndex) {
				case MEMBER_COLUMN:
					return fLabelProvider.getImage(element);
				case ACTION_COLUMN:
				default:
					return null;
			}
		}

		public String getColumnText(final Object element, final int columnIndex) {
			switch (columnIndex) {
				case MEMBER_COLUMN:
					return fLabelProvider.getText(element);
				case ACTION_COLUMN:
					if (element instanceof Feature)
						return "Clone";
				default:
					return null;
			}
		}
	}

	private static final int ACTION_COLUMN = 1;

	private static final int MEMBER_COLUMN = 0;

	protected static final int PULL_UP_ACTION = 0;

	protected List<Feature> fCandidateTypes;

	private Button fDeselectAllButton;

	private Button fSelectAllButton;
	
//	private Button checkCloneCodesButton;

	private Label fStatusLine;

	private Label fLabel;

	private Combo fSuperTypesCombo;

	private ContainerCheckedTreeViewer fTableViewer;

	private final PullUpRefactoring refactoring;

	public PullUpMemberPage(final String name, PullUpRefactoring refactoring) {
		super(name);
		this.refactoring = refactoring;
		setDescription(RefactoringMessages.PullUpInputPage1_page_message);
	}

	public PullUpRefactoring getPullUpMethodRefactoring() {
		return refactoring;
	}

	private boolean allMembersChecked() {
		final int count = fTableViewer.getTree().getItemCount();
		return getCheckedElements().size() == count;
	}

	@Override
	public boolean canFlipToNextPage() {
		return isPageComplete();
	}

	protected void checkPageCompletionStatus(final boolean displayErrors) {
		if (getCheckedElements().size() == 0) {
			if (displayErrors)
				setErrorMessage(getNoMembersMessage());
			setPageComplete(false);
		} else {
			setErrorMessage(null);
			setPageComplete(true);
		}
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
				setAllMembersChecked(true); 
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
				setAllMembersChecked(false); 
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
		final Tree tree= new Tree(parent, SWT.CHECK | SWT.BORDER | SWT.MULTI | SWT.V_SCROLL | SWT.H_SCROLL);
		tree.setLayoutData(new GridData(GridData.FILL_BOTH));
		tree.setHeaderVisible(true);
		tree.setLinesVisible(true);
		
//		tree.addListener(SWT.Selection, new Listener() {
//			   public void handleEvent(Event event) {
//			       if (event.detail == SWT.CHECK && event.item.getData() instanceof Feature){
//			          ((TreeItem)event.item).setChecked(true);
//			          ((TreeItem)event.item).setGrayed(true);
//			       } 
//			   }
//			});
		
		final TreeColumn column0 = new TreeColumn(tree, SWT.NONE);
		column0.setWidth(240);
		column0.setText(RefactoringMessages.PullUpInputPage1_Member);
		final TreeColumn column1 = new TreeColumn(tree, SWT.NONE);
		column1.setWidth(160);
//		column1.setText(RefactoringMessages.PullUpInputPage1_Action);

		fTableViewer = new ContainerCheckedTreeViewer(tree);
		fTableViewer.setUseHashlookup(true);
		final CloneSignatureMatcher cloneSignatureMatcher = new CloneSignatureMatcher(refactoring.getProjectSignatures(),refactoring.getFeatureProject(), refactoring.getSelectedElement(), refactoring.getFile());
		
		fTableViewer.setContentProvider(new PullUpHierarchyContentProvider(cloneSignatureMatcher.getMatchedClonedSignatures()));
		fTableViewer.setLabelProvider(new PullUpMemberLabelProvider());
		fTableViewer.setInput(refactoring.getPullableElements());
		fTableViewer.addSelectionChangedListener(new ISelectionChangedListener() {

			public void selectionChanged(final SelectionChangedEvent event) {
				updateButtonEnablement(event.getSelection());
			}
		});
		fTableViewer.addCheckStateListener(new ICheckStateListener() {

			public void checkStateChanged(final CheckStateChangedEvent event) {
				updateWizardPage(null, true);
			}
		});
		
//		fTableViewer.expandAll();
		
//		checkPullUp(refactoring.getPullableElements(), false);
		
		updateWizardPage(null, true);
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

	private void createSuperTypeCombo(Composite parent) {
		final Label label = new Label(parent, SWT.NONE);
		label.setText(RefactoringMessages.PullUpInputPage1_Select_destination);
		label.setLayoutData(new GridData());

		fSuperTypesCombo = new Combo(parent, SWT.READ_ONLY);
		SWTUtil.setDefaultVisibleItemCount(fSuperTypesCombo);
		if (fCandidateTypes.size() == 0) return;
		
		for (Feature feature : fCandidateTypes) {
			fSuperTypesCombo.add(feature.getName());
		}
		
		fSuperTypesCombo.select(fCandidateTypes.size() - 1);
		fSuperTypesCombo.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
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

	public Feature getDestinationType() {
		final int index = fSuperTypesCombo.getSelectionIndex();
		if (index >= 0)
			return fCandidateTypes.get(index);
		return null;
	}

	@Override
	public IWizardPage getNextPage() {
		initializeRefactoring();
//		if (getMethodsForAction(PULL_UP_ACTION).length == 0)
//			return computeSuccessorPage();
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

	protected int getTableRowCount() {
		return 10;
	}

	protected void initializeEnablement() {
		fTableViewer.getTree().setEnabled(true);
		fStatusLine.setEnabled(true);
		fLabel.setEnabled(true);
	}

	private void initializeRefactoring() {
		refactoring.setPullUpSignatures(getPullUpMembers());
		refactoring.setDeletableSignatures(getDeletableMembers());
		final Feature destination = getDestinationType();
		if (destination != null)
			refactoring.setDestinationFeature(destination);
	}

	private Set<ExtendedPullUpSignature> getPullUpMembers() {
		Set<ExtendedPullUpSignature> members = new HashSet<>();
	
		fTableViewer.expandAll();
		List<TreeItem> checkedItems = getCheckedElements();
		for (TreeItem treeItem : checkedItems) {
			members.add((ExtendedPullUpSignature) treeItem.getData());
		}
		
		return members;
	}

	private Set<ExtendedPullUpSignature> getDeletableMembers() {
		Set<ExtendedPullUpSignature> members = new HashSet<>();
		
		fTableViewer.expandAll();
		List<TreeItem> checkedItems = getCheckedElements();
		for (TreeItem treeItem : checkedItems) {
			
			final ExtendedPullUpSignature extSignature = (ExtendedPullUpSignature) treeItem.getData();
			if (treeItem.getItemCount() > 0)
			{
				for (TreeItem childItem : treeItem.getItems()) {
					final Feature feature = (Feature) childItem.getData();
					final int featureID = refactoring.getProjectSignatures().getFeatureID(feature.getName());
					members.add(new ExtendedPullUpSignature(extSignature.getSignature(),  featureID));
				}
			}
			else
			{
				members.add(extSignature);
			}
		}
		
		return members;
	}

	@Override
	protected boolean performFinish() {
		initializeRefactoring();
		return super.performFinish();
	}

	@Override
	public void setVisible(final boolean visible) {
		super.setVisible(visible);
		if (visible) {
			try {
				//refactoring.resetEnvironment();
			} finally {
//				fTableViewer.setSelection(new StructuredSelection(getActiveInfos()), true);
				fTableViewer.getControl().setFocus();
			}
		}
	}

	private void updateButtonEnablement(final ISelection selection) {
		if (fSelectAllButton != null)
			fSelectAllButton.setEnabled(!allMembersChecked());
		if (fDeselectAllButton != null)
			fDeselectAllButton.setEnabled(allMembersChecked());
	}

	private void updateStatusLine() {
		if (fStatusLine == null)
			return;
		
		List<TreeItem> checkedItems = getCheckedElements();
		final String msg = checkedItems.size() == 1 ? Messages.format(RefactoringMessages.PullUpInputPage1_status_line_singular,
				(new PullUpMemberLabelProvider()).getColumnText(checkedItems.get(0).getData(), MEMBER_COLUMN)) : Messages.format(
				RefactoringMessages.PullUpInputPage1_status_line_plural, String.valueOf(checkedItems.size()));
		fStatusLine.setText(msg);
	}

	private List<TreeItem> getCheckedElements() {
		List<TreeItem> checkedItems = new ArrayList<>();
		for (TreeItem treeItem : fTableViewer.getTree().getItems()) {
			if (treeItem.getChecked()) checkedItems.add(treeItem);
		}
		return checkedItems;
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

	private void setAllMembersChecked(final boolean checked) {
		for (TreeItem item : fTableViewer.getTree().getItems()) {
			for (TreeItem childItem : item.getItems()) {
				childItem.setChecked(checked);
			}
			item.setChecked(checked);
		}
	}
}
