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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jdt.internal.ui.IJavaHelpContextIds;
import org.eclipse.jdt.internal.ui.refactoring.RefactoringMessages;
import org.eclipse.jdt.internal.ui.util.SWTUtil;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTreeViewer;
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
import org.prop4j.Implies;
import org.prop4j.Node;

import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
//import de.ovgu.featureide.featurehouse.refactoring.RenameRefactoring;
//import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.Features;
//import de.ovgu.featureide.fm.core.Features;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.ui.views.collaboration.outline.CollaborationOutlineLabelProvider;

/**
 * Wizard page for pull up refactoring wizards which allows to specify the actions on the members to pull up.
 * 
 * @since 3.2
 */
@SuppressWarnings("restriction")
public class PullUpMemberPage extends UserInputWizardPage {

	private static class PullUpHierarchyContentProvider implements ITreeContentProvider {

		private Map<AbstractSignature, List<ClonedFeatures>> clonedSignatures;
		private final IFeature sourceFeature;

		public void dispose() {}

		public PullUpHierarchyContentProvider(IFeature feature) {
			sourceFeature = feature;
		}

		public Object[] getChildren(final Object parentElement) {

			Set<Object> elements = new HashSet<>();
			if ((parentElement instanceof AbstractSignature) && (clonedSignatures.containsKey(parentElement))) {
				for (ClonedFeatures clonedFeatures : clonedSignatures.get(parentElement)) {
					if (clonedFeatures.getFeatures().contains(sourceFeature)) {
						elements.addAll(clonedFeatures.getFeatures());
						break;
					}
				}
			}
			return elements.toArray();

		}

		public Object[] getElements(final Object inputElement) {
			return clonedSignatures.keySet().toArray();
		}

		public Object getParent(final Object element) {
			return null;
		}

		public boolean hasChildren(final Object element) {
			return getChildren(element).length > 0;
		}

		public void inputChanged(final Viewer viewer, final Object oldInput, final Object newInput) {
			this.clonedSignatures = (Map<AbstractSignature, List<ClonedFeatures>>) newInput;
		}
	}

	private static class PullUpMemberLabelProvider extends LabelProvider implements ITableLabelProvider {

		private ILabelProvider fLabelProvider = new CollaborationOutlineLabelProvider();

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
				if (element instanceof IFeature) return "Clone";
			default:
				return null;
			}
		}
	}

	private static final int ACTION_COLUMN = 1;

	private static final int MEMBER_COLUMN = 0;

	private Button fDeselectAllButton;

	private Button fSelectAllButton;

	private Label fStatusLine;

	private Label fLabel;

	private Combo parentFeatureCombo;

	private CheckboxTreeViewer fTableViewer;

	private final PullUpRefactoring refactoring;

	private static final String PAGE_NAME = "PullUpMemberPage";

	public PullUpMemberPage(PullUpRefactoringWizard wizard) {
		super(PAGE_NAME);
		this.refactoring = (PullUpRefactoring) wizard.getRefactoring();
		;
		setDescription("Select the destination feature and the members to pull up.");
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
			if (displayErrors) setErrorMessage(getNoMembersMessage());
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

		createParentFeatureCombo(composite);
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
		final Tree tree = new Tree(parent, SWT.CHECK | SWT.BORDER | SWT.MULTI | SWT.V_SCROLL | SWT.H_SCROLL);
		tree.setLayoutData(new GridData(GridData.FILL_BOTH));
		tree.setHeaderVisible(true);
		tree.setLinesVisible(true);

		tree.addListener(SWT.Selection, new Listener() {

			public void handleEvent(Event event) {
//			       if (event.detail == SWT.CHECK && event.item.getData() instanceof Feature){
//			          ((TreeItem)event.item).setChecked(true);
//			          ((TreeItem)event.item).setGrayed(true);
//			       } 

				final Object item = event.item.getData();
				final TreeItem treeItem = (TreeItem) event.item;
				if (item instanceof IFeature) checkSignature(treeItem);
				else checkChildren(treeItem);
			}
		});

		final TreeColumn column0 = new TreeColumn(tree, SWT.NONE);
		column0.setWidth(240);
		column0.setText(RefactoringMessages.PullUpInputPage1_Member);
		final TreeColumn column1 = new TreeColumn(tree, SWT.NONE);
		column1.setWidth(160);
//		column1.setText(RefactoringMessages.PullUpInputPage1_Action);

		fTableViewer = new CheckboxTreeViewer(tree);
		fTableViewer.setUseHashlookup(true);

		final Map<AbstractSignature, List<ClonedFeatures>> signatures = refactoring.getClonedSignatures();
		for (AbstractSignature signature : refactoring.getPullableElements()) {
			if (!signatures.containsKey(signature)) signatures.put(signature, Collections.<ClonedFeatures> emptyList());
		}

		fTableViewer.setContentProvider(new PullUpHierarchyContentProvider(refactoring.getSourceFeature()));
		fTableViewer.setLabelProvider(new PullUpMemberLabelProvider());
		fTableViewer.setInput(signatures);
		fTableViewer.addSelectionChangedListener(new ISelectionChangedListener() {

			public void selectionChanged(final SelectionChangedEvent event) {
				updateButtonEnablement(event.getSelection());
			}
		});
		fTableViewer.addCheckStateListener(new ICheckStateListener() {

			public void checkStateChanged(final CheckStateChangedEvent event) {
				updateWizardPage(null, true);
				fillParentFeatureComboBox(getSelectedPullUpFeatures());

				final int itemCount = parentFeatureCombo.getItemCount();
				if (itemCount > 1) parentFeatureCombo.select(itemCount - 1);
			}
		});

		fTableViewer.expandAll();
		updateWizardPage(null, true);
	}

	private void checkSignature(TreeItem checkedItem) {

		TreeItem parentItem = getParent(checkedItem);
		if (parentItem == null) return;

		boolean isCheckItemClassSignature = parentItem.getData() instanceof AbstractClassSignature;

		for (TreeItem item : fTableViewer.getTree().getItems()) {

			if (parentItem.equals(item)) parentItem.setChecked(checkedItem.getChecked() || atLeastOneChildrenChecked(item));
			else uncheckedItems(isCheckItemClassSignature, item);
		}
	}

	private void uncheckedItems(boolean isCheckItemClassSignature, TreeItem item) {
		if (isCheckItemClassSignature) {
			item.setChecked(false);
			checkAllChildren(false, item);
		} else if (item.getData() instanceof AbstractClassSignature) {
			item.setChecked(false);
			checkAllChildren(false, item);
		}
	}

	private boolean atLeastOneChildrenChecked(TreeItem item) {
		for (TreeItem childItem : item.getItems()) {
			if (childItem.getChecked()) return true;
		}

		return false;
	}

	private TreeItem getParent(TreeItem item) {
		for (TreeItem parentItem : fTableViewer.getTree().getItems()) {

			for (TreeItem childItem : parentItem.getItems()) {
				if (item.equals(childItem)) return parentItem;
			}
		}

		return null;
	}

	private void checkChildren(TreeItem checkedItem) {
		boolean isCheckItemClassSignature = checkedItem.getData() instanceof AbstractClassSignature;
		for (TreeItem item : fTableViewer.getTree().getItems()) {

			if (item.equals(checkedItem)) checkAllChildren(item.getChecked(), item);
			else uncheckedItems(isCheckItemClassSignature, item);
		}
	}

	private void checkAllChildren(boolean check, TreeItem item) {
		for (TreeItem childItem : item.getItems()) {
			childItem.setChecked(check);
		}
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

	private void createParentFeatureCombo(Composite parent) {
		final Label label = new Label(parent, SWT.NONE);
		label.setText("&Select destination feature:");
		label.setLayoutData(new GridData());

		parentFeatureCombo = new Combo(parent, SWT.READ_ONLY);
		SWTUtil.setDefaultVisibleItemCount(parentFeatureCombo);
		parentFeatureCombo.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));

		final ArrayList<IFeature> features = new ArrayList<>();
		features.add(refactoring.getSourceFeature());
		fillParentFeatureComboBox(features);
	}

	private IFeature determineDestinationFeature(final List<String> allFeatures) {
		final Map<String, List<String>> implies = getImplies();

		for (Entry<String, List<String>> implied : implies.entrySet()) {

			final List<String> impliedFeatures = implied.getValue();
			if (impliedFeatures.size() == allFeatures.size() && impliedFeatures.containsAll(allFeatures))
				return refactoring.getFeatureProject().getFeatureModel().getFeature(implied.getKey());
		}
		return null;
	}

	private List<String> getFeaturesNames(final List<IFeature> features) {
		List<String> allFeatures = new ArrayList<>();
		for (IFeature feature : features) {
			allFeatures.add(feature.getName());
		}
		return allFeatures;
	}

	private Map<String, List<String>> getImplies() {
		final Map<String, List<String>> implies = new HashMap<>();
		final List<IConstraint> constraints = refactoring.getFeatureProject().getFeatureModel().getConstraints();

		for (IConstraint constraint : constraints) {
			if (!(constraint.getNode() instanceof Implies)) continue;

			final Node[] children = constraint.getNode().getChildren();
			if (children.length != 2) continue;

			final String left = children[0].toString();
			final String right = children[1].toString();

			List<String> features = getImpliesFeatures(implies, right);
			features.add(left);
		}
		return implies;
	}

	private List<String> getImpliesFeatures(final Map<String, List<String>> implies, final String right) {
		List<String> features;
		if (implies.containsKey(right)) features = implies.get(right);
		else {
			features = new ArrayList<>();
			implies.put(right, features);
		}
		return features;
	}

	private void fillParentFeatureComboBox(List<IFeature> features) {
		final List<IFeature> commonAncestors = Features.getCommonAncestors(features);

		parentFeatureCombo.removeAll();

		for (IFeature feature : commonAncestors) {
			if (feature.equals(refactoring.getSourceFeature())) continue;
			parentFeatureCombo.add(feature.getName());
		}

//		parentFeatureCombo.removeAll();
//		for (String feature : getImplies().keySet()) {
//				parentFeatureCombo.add(feature);
//		}

//		final Feature feature = determineDestinationFeature(getFeaturesNames(features));
//		if (feature != null)
//		{
//			parentFeatureCombo.add(feature.getName());
//		
//		if (features == null || features.size() == 0) return;
//		
//		for (Feature feature : commonAncestors) {
//			if (feature.equals(refactoring.getSourceFeature())) continue;
//			parentFeatureCombo.add(feature.getName());
//		}

//		parentFeatureCombo.select(parentFeatureCombo.getItemCount() - 1);
//		}
	}

	@Override
	public void dispose() {
		fTableViewer = null;
		super.dispose();
	}

	public IFeature getDestinationFeature() {
		final String featureName = parentFeatureCombo.getText();
		if (featureName.isEmpty()) return null;

		return refactoring.getFeatureProject().getFeatureModel().getFeature(featureName);
	}

	@Override
	public IWizardPage getNextPage() {
		initializeRefactoring();
//		if (getMethodsForAction(PULL_UP_ACTION).length == 0)
//			return computeSuccessorPage();
		return super.getNextPage();
	}

	protected String getNoMembersMessage() {
		return "No members selected to pull up";
	}

	protected String getPullUpActionLabel() {
		return RefactoringMessages.PullUpInputPage1_pull_up;
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
		final IFeature destination = (IFeature) getDestinationFeature();
		if (destination != null) refactoring.setDestinationFeature(destination);
		refactoring.setPullUpSignatures(getPullUpMembers(destination));
		refactoring.setDeletableSignatures(getDeletableMembers(destination));
	}

	private Set<ExtendedPullUpSignature> getPullUpMembers(final IFeature destinationFeature) {
		Set<ExtendedPullUpSignature> members = new HashSet<>();

		fTableViewer.expandAll();
		List<TreeItem> checkedItems = getCheckedElements();
		boolean existSignatureInDestinationFeature = false;
		for (TreeItem treeItem : checkedItems) {

			existSignatureInDestinationFeature = false;
			for (TreeItem childItem : treeItem.getItems()) {
				if (childItem.getData().equals(destinationFeature)) {
					existSignatureInDestinationFeature = true;
					break;
				}
			}
			if (!existSignatureInDestinationFeature) {
				final int featureID = refactoring.getProjectSignatures().getFeatureID(refactoring.getSourceFeature().getName());
				members.add(new ExtendedPullUpSignature((AbstractSignature) treeItem.getData(), featureID));
			}
		}

		return members;
	}

	private Set<ExtendedPullUpSignature> getDeletableMembers(final IFeature destinationFeature) {
		Set<ExtendedPullUpSignature> members = new HashSet<>();

		fTableViewer.expandAll();
		List<TreeItem> checkedItems = getCheckedElements();
		for (TreeItem treeItem : checkedItems) {

			final AbstractSignature signature = (AbstractSignature) treeItem.getData();
			if (treeItem.getItemCount() > 0) {
				for (TreeItem childItem : treeItem.getItems()) {
					if (!childItem.getChecked()) continue;

					final IFeature feature = (IFeature) childItem.getData();
					if (feature.equals(destinationFeature)) continue;

					final int featureID = refactoring.getProjectSignatures().getFeatureID(feature.getName());
					members.add(new ExtendedPullUpSignature(signature, featureID));
				}
			} else {
				final int featureID = refactoring.getProjectSignatures().getFeatureID(refactoring.getSourceFeature().getName());
				members.add(new ExtendedPullUpSignature((AbstractSignature) treeItem.getData(), featureID));
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
				// refactoring.resetEnvironment();
			} finally {
//				fTableViewer.setSelection(new StructuredSelection(getActiveInfos()), true);
				fTableViewer.getControl().setFocus();
			}
		}
	}

	private void updateButtonEnablement(final ISelection selection) {
		if (fSelectAllButton != null) fSelectAllButton.setEnabled(!allMembersChecked());
		if (fDeselectAllButton != null) fDeselectAllButton.setEnabled(allMembersChecked());
	}

	private void updateStatusLine() {
		if (fStatusLine == null) return;

		List<TreeItem> checkedItems = getCheckedElements();
		final String msg = checkedItems.size() == 1
			? Messages.format(RefactoringMessages.PullUpInputPage1_status_line_singular,
					(new PullUpMemberLabelProvider()).getColumnText(checkedItems.get(0).getData(), MEMBER_COLUMN))
			: Messages.format(RefactoringMessages.PullUpInputPage1_status_line_plural, String.valueOf(checkedItems.size()));
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

	private List<IFeature> getSelectedPullUpFeatures() {
		List<IFeature> features = new ArrayList<>();
		features.add(refactoring.getSourceFeature());
		for (TreeItem item : fTableViewer.getTree().getItems()) {
			for (TreeItem childItem : item.getItems()) {
				IFeature feature = (IFeature) childItem.getData();
				if (childItem.getChecked() && !features.contains(feature)) features.add(feature);
			}
		}
		return features;
	}

}
