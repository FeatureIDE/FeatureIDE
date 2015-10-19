package de.ovgu.featureide.featurehouse.refactoring.pullUp;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.ITypeHierarchy;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.corext.refactoring.RefactoringCoreMessages;
import org.eclipse.jdt.internal.corext.refactoring.util.JavaElementUtil;
import org.eclipse.jdt.internal.corext.util.Messages;
import org.eclipse.jdt.internal.corext.util.Strings;
import org.eclipse.jdt.internal.ui.IJavaHelpContextIds;
import org.eclipse.jdt.internal.ui.JavaPlugin;
import org.eclipse.jdt.internal.ui.javaeditor.JavaSourceViewer;
import org.eclipse.jdt.internal.ui.refactoring.RefactoringMessages;
import org.eclipse.jdt.internal.ui.util.ExceptionHandler;
import org.eclipse.jdt.internal.ui.util.SWTUtil;
import org.eclipse.jdt.ui.JavaElementComparator;
import org.eclipse.jdt.ui.JavaElementLabels;
import org.eclipse.jdt.ui.PreferenceConstants;
import org.eclipse.jdt.ui.text.JavaSourceViewerConfiguration;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.ltk.ui.refactoring.UserInputWizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.text.edits.DeleteEdit;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.ContainerCheckedTreeViewer;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;
import org.eclipse.ui.texteditor.IDocumentProvider;

import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.SignaturePosition;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringUtil;
import de.ovgu.featureide.fm.core.Feature;


@SuppressWarnings("restriction")
public class PullUpMethodPage extends UserInputWizardPage {
	
	private static class PullUpHierarchyContentProvider implements ITreeContentProvider {

		private Set<FeatureSignatureHierarchy> hierarchies;
		
		public PullUpHierarchyContentProvider() {
		}

		public void dispose() {
			hierarchies = null;
		}

		public Object[] getChildren(final Object parentElement) {
			Set<Object> elements = new HashSet<>();
			if (parentElement instanceof Feature)
				elements.addAll(getChildrenForFeature((Feature) parentElement));
			else if (parentElement instanceof ExtendedPullUpSignature)
				elements.addAll(((ExtendedPullUpSignature) parentElement).getChildren());
			
			return elements.toArray();
		}

		public Object[] getElements(final Object inputElement) {
			Set<Object> elements = new HashSet<>();
			for (FeatureSignatureHierarchy hierarchy : hierarchies) {
				elements.add(hierarchy.getFeature());
			}
			return elements.toArray();
		}

		public Object getParent(final Object element) {
			if (element instanceof ExtendedPullUpSignature)
				return ((ExtendedPullUpSignature) element).getParent();
				
			return null;
		}
		
		public boolean hasChildren(final Object element) {
			return getChildren(element).length > 0;
		}
		
		public void inputChanged(final Viewer viewer, final Object oldInput, final Object newInput) {
			hierarchies = (Set<FeatureSignatureHierarchy>) newInput;
		}
		
		private Set<ExtendedPullUpSignature> getChildrenForFeature(Feature feature)
		{
			for (FeatureSignatureHierarchy hierarchy : hierarchies) {
				if (feature.equals(hierarchy.getFeature()))
						return hierarchy.getChildren();
			}
			
			return Collections.emptySet();
		}
	}
	
	private static final String PAGE_NAME= "PullUpMethodPage"; //$NON-NLS-1$

	private boolean fChangedSettings= true;

	private Label fSelectionLabel;

	private SourceViewer fSourceViewer;

	private ContainerCheckedTreeViewer fTreeViewer;

	private Label fTypeHierarchyLabel;

	private final PullUpRefactoring<AbstractSignature> refactoring;
	
	@SuppressWarnings("unchecked")
	public PullUpMethodPage(PullUpRefactoring refactoring) {
		super(PAGE_NAME);
		this.refactoring = refactoring;
		setMessage(RefactoringMessages.PullUpInputPage_select_methods);
	}
	
	private void checkAllParents(final IType parent) {
		final ITypeHierarchy th= getTreeInput();
		final IType root= getTreeInput().getType();
		IType type= parent;
		while (!root.equals(type)) {
			fTreeViewer.setChecked(type, true);
			type= th.getSuperclass(type);
		}
		fTreeViewer.setChecked(root, true);
	}

	public void checkPulledUp() {
		uncheckAll();
		fTreeViewer.setCheckedElements(refactoring.getPullUpSignatures());
		final ExtendedPullUpSignature parent = refactoring.getDestinationType();
		fTreeViewer.setChecked(parent, true);
//		checkAllParents(parent);
	}

	private void createButtonComposite(final Composite superComposite) {
		final Composite buttonComposite= new Composite(superComposite, SWT.NONE);
		buttonComposite.setLayoutData(new GridData(GridData.FILL, GridData.BEGINNING, true, false));
		final GridLayout layout= new GridLayout(2, false);
		layout.marginWidth= 0;
		buttonComposite.setLayout(layout);

		fSelectionLabel= new Label(buttonComposite, SWT.LEFT | SWT.WRAP | SWT.HORIZONTAL);
		GridData data= new GridData(GridData.BEGINNING, GridData.BEGINNING, true, false);
		data.widthHint= convertWidthInCharsToPixels(32);
		fSelectionLabel.setLayoutData(data);

		final Button button= new Button(buttonComposite, SWT.PUSH);
		button.setText(RefactoringMessages.PullUpInputPage2_Select);
		button.setLayoutData(new GridData());
		SWTUtil.setButtonDimensionHint(button);
		button.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(final SelectionEvent e) {
				checkPulledUp();
				updateSelectionLabel();
			}
		});
	}

	public void createControl(final Composite parent) {
		final Composite composite= new Composite(parent, SWT.NONE);
		composite.setLayout(new GridLayout());

		createTreeAndSourceViewer(composite);
		createButtonComposite(composite);
		setControl(composite);

		Dialog.applyDialogFont(composite);
		PlatformUI.getWorkbench().getHelpSystem().setHelp(getControl(), IJavaHelpContextIds.PULL_UP_WIZARD_PAGE);
	}

	private void createHierarchyTreeComposite(final Composite parent) {
		final Composite composite= new Composite(parent, SWT.NONE);
		composite.setLayoutData(new GridData(GridData.FILL_BOTH));
		final GridLayout layout= new GridLayout();
		layout.marginWidth= 0;
		layout.marginHeight= 0;
		layout.horizontalSpacing= 1;
		layout.verticalSpacing= 1;
		composite.setLayout(layout);

		createTypeHierarchyLabel(composite);
		createTreeViewer(composite);
	}

	private void createSourceViewer(final Composite c) {
		final IPreferenceStore store= JavaPlugin.getDefault().getCombinedPreferenceStore();
		fSourceViewer= new JavaSourceViewer(c, null, null, false, SWT.V_SCROLL | SWT.H_SCROLL | SWT.MULTI | SWT.BORDER | SWT.FULL_SELECTION, store);
		fSourceViewer.configure(new JavaSourceViewerConfiguration(JavaPlugin.getDefault().getJavaTextTools().getColorManager(), store, null, null));
		fSourceViewer.setEditable(false);
		fSourceViewer.getControl().setLayoutData(new GridData(GridData.FILL_BOTH));
		fSourceViewer.getControl().setFont(JFaceResources.getFont(PreferenceConstants.EDITOR_TEXT_FONT));
	}

	private void createSourceViewerComposite(final Composite parent) {
		final Composite c= new Composite(parent, SWT.NONE);
		c.setLayoutData(new GridData(GridData.FILL_BOTH));
		final GridLayout layout= new GridLayout();
		layout.marginWidth= 0;
		layout.marginHeight= 0;
		layout.horizontalSpacing= 1;
		layout.verticalSpacing= 1;
		c.setLayout(layout);

		createSourceViewerLabel(c);
		createSourceViewer(c);
	}

	private void createSourceViewerLabel(final Composite c) {
		final Label label= new Label(c, SWT.WRAP);
		final GridData gd= new GridData(GridData.FILL_HORIZONTAL);
		label.setText(RefactoringMessages.PullUpInputPage2_Source);
		label.setLayoutData(gd);
	}

	private void createTreeAndSourceViewer(final Composite superComposite) {
		final SashForm composite= new SashForm(superComposite, SWT.HORIZONTAL);
		initializeDialogUnits(superComposite);
		final GridData gd= new GridData(GridData.FILL_BOTH);
		gd.heightHint= convertHeightInCharsToPixels(20);
		gd.widthHint= convertWidthInCharsToPixels(10);
		composite.setLayoutData(gd);
		final GridLayout layout= new GridLayout();
		layout.numColumns= 2;
		layout.marginWidth= 0;
		layout.marginHeight= 0;
		layout.horizontalSpacing= 1;
		layout.verticalSpacing= 1;
		composite.setLayout(layout);

		createHierarchyTreeComposite(composite);
		createSourceViewerComposite(composite);
		composite.setWeights(new int[] { 50, 50});
	}

	private void createTreeViewer(final Composite composite) {
		final Tree tree= new Tree(composite, SWT.CHECK | SWT.BORDER | SWT.MULTI | SWT.V_SCROLL | SWT.H_SCROLL);
		tree.setLayoutData(new GridData(GridData.FILL_BOTH));
		fTreeViewer= new ContainerCheckedTreeViewer(tree);
		fTreeViewer.setLabelProvider(new PullUpHierarchyLabelProvider());
		fTreeViewer.setUseHashlookup(true);
		fTreeViewer.setComparator(new JavaElementComparator());
		fTreeViewer.addSelectionChangedListener(new ISelectionChangedListener() {

			public void selectionChanged(final SelectionChangedEvent event) {
				treeViewerSelectionChanged(event);
			}
		});
		fTreeViewer.addCheckStateListener(new ICheckStateListener() {

			public void checkStateChanged(final CheckStateChangedEvent event) {
				updateSelectionLabel();
			}
		});
	}

	private void createTypeHierarchyLabel(final Composite composite) {
		fTypeHierarchyLabel= new Label(composite, SWT.WRAP);
		final GridData gd= new GridData(GridData.FILL_HORIZONTAL);
		fTypeHierarchyLabel.setLayoutData(gd);
	}

	public void fireSettingsChanged() {
		fChangedSettings= true;
	}

	private Set<ExtendedPullUpSignature> getCheckedMethods() {
		final Object[] checked= fTreeViewer.getCheckedElements();
		final Set<ExtendedPullUpSignature> members = new HashSet<>();
		for (int i= 0; i < checked.length; i++) {
			if (checked[i] instanceof ExtendedPullUpSignature && ((ExtendedPullUpSignature) checked[i]).getSignature() instanceof AbstractMethodSignature)
			{
				members.add((ExtendedPullUpSignature) checked[i]);
			}
		}
		return members;
	}

	private ExtendedPullUpSignature getFirstSelectedSourceReference(final SelectionChangedEvent event) {
		final ISelection s= event.getSelection();
		if (!(s instanceof IStructuredSelection))
			return null;
		final IStructuredSelection ss= (IStructuredSelection) s;
		if (ss.size() != 1)
			return null;
		final Object first= ss.getFirstElement();
		if (!(first instanceof ExtendedPullUpSignature))
			return null;
		return (ExtendedPullUpSignature) first;
	}

	@Override
	public IWizardPage getNextPage() {
		initializeRefactoring();
		return super.getNextPage();
	}

	private ITypeHierarchy getTreeInput() {
		return (ITypeHierarchy) fTreeViewer.getInput();
	}

	private void initializeRefactoring() {
		refactoring.setDeletedMethods(getCheckedMethods());
	}

	private void initializeTreeViewer() {
		try {
			getContainer().run(false, false, new IRunnableWithProgress() {

				public void run(final IProgressMonitor pm) {
					try {
						initializeTreeViewer(pm);
					} finally {
						pm.done();
					}
				}
			});
		} catch (InvocationTargetException e) {
			ExceptionHandler.handle(e, getShell(), RefactoringMessages.PullUpInputPage_pull_Up, RefactoringMessages.PullUpInputPage_exception);
		} catch (InterruptedException e) {
			Assert.isTrue(false);
		}
	}

	private void initializeTreeViewer(final IProgressMonitor pm) {
		try {
			pm.beginTask(RefactoringCoreMessages.PullUpRefactoring_checking, 2);
			removeAllTreeViewFilters();
			fTreeViewer.setContentProvider(new PullUpHierarchyContentProvider());
			fTreeViewer.setInput(new FeatureSignatureHierarchyCreator(refactoring.getDestinationType(), 
					refactoring.getProjectSignatures(), refactoring.getPullUpSignatures()).createFeatureHierarchies());
			precheckElements(fTreeViewer);
			fTreeViewer.expandAll();
			updateSelectionLabel();
		} finally {
			pm.done();
		}
	}

	@Override
	protected boolean performFinish() {
		initializeRefactoring();
		return super.performFinish();
	}

	private void precheckElements(final ContainerCheckedTreeViewer treeViewer) {
		final AbstractSignature[] members = refactoring.getPullUpSignatures();
		for (int i= 0; i < members.length; i++) {
			//treeViewer.setChecked(members[i], true);
		}
	}

	private void removeAllTreeViewFilters() {
		final ViewerFilter[] filters= fTreeViewer.getFilters();
		for (int i= 0; i < filters.length; i++) {
			fTreeViewer.removeFilter(filters[i]);
		}
	}

	private void setHierarchyLabelText() {
		final String message= Messages.format(RefactoringMessages.PullUpInputPage_subtypes, refactoring.getDestinationType().getSignature().getFullName());
		fTypeHierarchyLabel.setText(message);
	}

	private void setSourceViewerContents(ExtendedPullUpSignature signature) {
		String content = null;
		if (signature != null) {
			
			final AFeatureData featureData = getFeatureDataForId(signature.getSignature(), signature.getFeatureId());
			if (featureData != null)
			{
				SignaturePosition position = featureData.getSigPosition();
				IFile ifile = RefactoringUtil.getFile(featureData.getAbsoluteFilePath());
	
				IDocumentProvider provider = new TextFileDocumentProvider();
				try {
					provider.connect(ifile);
					final IDocument doc = provider.getDocument(ifile);
					
					int startOffset = doc.getLineOffset(position.getStartRow() - 1) + position.getStartColumn() -1;
					int endOffset = doc.getLineOffset(position.getEndRow() - 1) + position.getEndColumn();
					content = doc.get(startOffset, endOffset-startOffset);
					
					ICompilationUnit compilationUnit = RefactoringUtil.getCompilationUnit(featureData.getAbsoluteFilePath());
	                IJavaProject project = compilationUnit == null ? null:  compilationUnit.getJavaProject();
	                IRegion region = doc.getLineInformationOfOffset(endOffset);
	                String lineContent = doc.get(region.getOffset(), region.getLength());
	                final int indent = Strings.computeIndentUnits(lineContent, project);
	                content = Strings.changeIndent(content, indent, project, "", "\n");
					
				} catch (CoreException e) {
					e.printStackTrace();
				} catch (BadLocationException e) {
					e.printStackTrace();
				}
			}
		}
		final IDocument document= (content == null) ? new Document() : new Document(content);
		JavaPlugin.getDefault().getJavaTextTools().setupJavaDocumentPartitioner(document);
		fSourceViewer.setDocument(document);
	}
	
	private AFeatureData getFeatureDataForId(final AbstractSignature signature, final int featureId){
		for (AFeatureData featureData : signature.getFeatureData()) {
			if (featureData.getID() == featureId) return featureData;
		}
		return null;
	}

	@Override
	public void setVisible(final boolean visible) {
		if (visible && fChangedSettings) {
			fChangedSettings= false;
			initializeTreeViewer();
			setHierarchyLabelText();
		}
		super.setVisible(visible);
	}

	private void showInSourceViewer(final ExtendedPullUpSignature selected) throws JavaModelException {
		if (selected == null)
			setSourceViewerContents(null);
		else
			setSourceViewerContents(selected);
	}

	private void treeViewerSelectionChanged(final SelectionChangedEvent event) {
		try {
			showInSourceViewer(getFirstSelectedSourceReference(event));
		} catch (JavaModelException e) {
			ExceptionHandler.handle(e, RefactoringMessages.PullUpInputPage_pull_up1, RefactoringMessages.PullUpInputPage_see_log);
		}
	}

	private void uncheckAll() {
		final IType root= getTreeInput().getType();
		fTreeViewer.setChecked(root, false);
	}

	private void updateSelectionLabel() {
		Set<ExtendedPullUpSignature> methods= getCheckedMethods();
		int checkedMethodsCount= methods.size();
		String text= checkedMethodsCount == 1 ? Messages.format(RefactoringMessages.PullUpInputPage_hierarchyLabal_singular, new PullUpHierarchyLabelProvider().getText(methods.iterator().next().getSignature())) : 
			Messages.format(RefactoringMessages.PullUpInputPage_hierarchyLabal_plural, String.valueOf(checkedMethodsCount));
		fSelectionLabel.setText(text);

	}
	
}