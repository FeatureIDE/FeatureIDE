/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.views.collaboration.outline;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeExpansionEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors.SetFeatureColorAction;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineTreeContentProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.action.FilterOutlineAction;
import de.ovgu.featureide.fm.ui.views.outline.custom.filters.IOutlineFilter;
import de.ovgu.featureide.ui.views.collaboration.outline.filters.HideAllFields;
import de.ovgu.featureide.ui.views.collaboration.outline.filters.HideAllMethods;
import de.ovgu.featureide.ui.views.collaboration.outline.filters.SortByOccurrenceInFeature;

/**
 *
 * Provides the content for the collaboration outline.
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Stefan Krüger
 * @author Florian Proksch
 * @author Dominic Labsch
 * @author Daniel P�sche
 * @author Reimar Schröter
 * @author Christopher Sontag
 */
public class ExtendedOutline extends OutlineProvider {

	private static final Set<String> supportedTypes = new HashSet<>();
	static {
		supportedTypes.add("java");
		supportedTypes.add("jak");
		supportedTypes.add("hs");
		supportedTypes.add("h");
		supportedTypes.add("c");
		supportedTypes.add("cs");
		supportedTypes.add("asm");
	}

	private TreeViewer viewer;
	private IFile file;
	private IFeatureModel featureModel;

	public ExtendedOutline() {
		super(new ExtendedContentProvider(), new ExtendedOutlineLabelProvider());
	}

	@Override
	public boolean isSupported(IFile file) {
		return supportedTypes.contains(file.getFileExtension());
	}

	@Override
	public void handleUpdate(TreeViewer viewer, IFile iFile) {
		this.viewer = viewer;
		file = iFile;

		if ((iFile != null) && (CorePlugin.getFeatureProject(iFile) != null)) {
			featureModel = CorePlugin.getFeatureProject(iFile).getFeatureModel();
		}
	}

	@Override
	protected void initContextMenuActions(IMenuManager manager) {
		if (featureModel != null) {
			final SetFeatureColorAction setFeatureColorAction = new SetFeatureColorAction(viewer, featureModel);

			final Object sel = ((IStructuredSelection) viewer.getSelection()).getFirstElement();

			if ((sel instanceof RoleElement) && !(sel instanceof FSTDirective)) {
				manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
				final List<IFeature> featureList = new ArrayList<>();

				for (final Object obj : ((IStructuredSelection) viewer.getSelection()).toArray()) {
					final RoleElement<?> method = (RoleElement<?>) obj;
					final ITreeContentProvider contentProvider = (ITreeContentProvider) viewer.getContentProvider();
					for (final Object role : contentProvider.getChildren(method)) {
						final FSTFeature fst = ((FSTRole) role).getFeature();
						featureList.add(featureModel.getFeature(fst.getName()));
					}
				}
				setFeatureColorAction.updateFeatureList(new StructuredSelection(featureList));
				manager.add(setFeatureColorAction);
			}

			else if (sel instanceof FSTRole) {
				manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
				final List<IFeature> featureList = new ArrayList<>();

				for (final Object obj : ((IStructuredSelection) viewer.getSelection()).toArray()) {
					final FSTRole role = (FSTRole) obj;
					final FSTFeature feature = role.getFeature();
					featureList.add(featureModel.getFeature(feature.getName()));
				}

				setFeatureColorAction.updateFeatureList(new StructuredSelection(featureList));
				manager.add(setFeatureColorAction);
			}

			else if (sel instanceof FSTDirective) {
				manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
				final List<IFeature> featureList = new ArrayList<>();

				for (final Object obj : ((IStructuredSelection) viewer.getSelection()).toArray()) {
					final FSTDirective fst = (FSTDirective) obj;
					final String featureName = fst.getFeatureNames().get(0);
					final IFeature feature = featureModel.getFeature(featureName);
					featureList.add(feature);
				}
				setFeatureColorAction.updateFeatureList(new StructuredSelection(featureList));
				manager.add(setFeatureColorAction);
			}
		}
	}

	@Override
	protected void initToolbarActions(IToolBarManager manager) {
		final FilterOutlineAction hideAllFields = new FilterOutlineAction(new HideAllFields()) {

			@Override
			public void run() {
				final OutlineTreeContentProvider treeProvider = getTreeProvider();
				if (!treeProvider.hasFilter(getFilter())) {
					treeProvider.addFilter(getFilter());
				} else {
					treeProvider.removeFilter(getFilter());
				}
				viewer.setInput(file);
			}
		};
		manager.add(hideAllFields);
		final FilterOutlineAction hideAllMethods = new FilterOutlineAction(new HideAllMethods()) {

			@Override
			public void run() {
				final OutlineTreeContentProvider treeProvider = getTreeProvider();
				if (!treeProvider.hasFilter(getFilter())) {
					treeProvider.addFilter(getFilter());
				} else {
					treeProvider.removeFilter(getFilter());
				}
				viewer.setInput(file);
			}
		};
		manager.add(hideAllMethods);
		final FilterOutlineAction sortByOccurrenceInFeature = new FilterOutlineAction(new SortByOccurrenceInFeature()) {

			@Override
			public void run() {
				final OutlineTreeContentProvider treeProvider = getTreeProvider();
				if (!treeProvider.hasFilter(getFilter())) {
					treeProvider.addFilter(getFilter());
				} else {
					treeProvider.removeFilter(getFilter());
				}
				viewer.setInput(file);
			}
		};
		manager.add(sortByOccurrenceInFeature);
	}

	@Override
	protected List<IOutlineFilter> getFilters() {
		return null;
	}

	/**
	 * triggers a scrolling action to the selected field/method in the current editor
	 */
	@Override
	public void selectionChanged(SelectionChangedEvent event) {
		if (file != null) {
			final IWorkbench workbench = PlatformUI.getWorkbench();
			final IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
			final IWorkbenchPage page = window.getActivePage();
			final IEditorPart activeEditor = page.getActiveEditor();

			// if a method or field is selected, the selection's FSTRole is always the first role of the first feature in the respective expandable
			// list in the outline no matter if the currently opened file contains the method.
			Object selection = ((IStructuredSelection) viewer.getSelection()).getFirstElement();
			FSTRole r = null;
			boolean fileAlreadyOpen = false;
			if (selection instanceof FSTRole) {
				r = (FSTRole) selection;
				selection = viewer.getTree().getSelection()[0].getParentItem().getData();
			} else if (selection instanceof FSTMethod) {
				final FSTMethod meth = ((FSTMethod) selection);
				fileAlreadyOpen = meth.getFile().getName().equals(file.getName()) && (getMethodLine(file, meth) > 0);
				r = meth.getRole();
				if (meth.getLine() != -1) {
					scrollToLine(activeEditor, meth.getLine());
				}
			} else if (selection instanceof FSTField) {
				final FSTField field = ((FSTField) selection);
				fileAlreadyOpen = field.getFile().getName().equals(file.getName()) && (getFieldLine(file, field) > 0);
				r = field.getRole();
			} else if (selection instanceof FSTInvariant) {
				final FSTInvariant invariant = ((FSTInvariant) selection);
				fileAlreadyOpen = invariant.getFile().getName().equals(file.getName()) && (getInvariantLine(file, invariant) > 0);
				r = invariant.getRole();
			} else if (selection instanceof FSTDirective) {
				fileAlreadyOpen = true;

			} else if (selection instanceof FSTClassFragment) {
				final FSTClassFragment innerClass = ((FSTClassFragment) selection);
				fileAlreadyOpen = innerClass.getFile().getName().equals(file.getName()) && (getClassFragmentLine(file, innerClass) > 0);
				r = innerClass.getRole();
			}

			else {
				return;
			}
			if (!fileAlreadyOpen && r.getFile().isAccessible()) {

				IContentType contentType = null;
				try {
					file = r.getFile();
					final IContentDescription description = file.getContentDescription();
					if (description != null) {
						contentType = description.getContentType();
					}
					IEditorDescriptor desc = null;
					if (contentType != null) {
						desc = workbench.getEditorRegistry().getDefaultEditor(file.getName(), contentType);
					} else {
						desc = workbench.getEditorRegistry().getDefaultEditor(file.getName());
					}
					if (desc != null) {
						page.openEditor(new FileEditorInput(file), desc.getId());
					} else {
						// case: there is no default editor for the file
						page.openEditor(new FileEditorInput(file), "org.eclipse.ui.DefaultTextEditor");
					}

				} catch (final CoreException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}

			if (selection instanceof FSTMethod) {
				final FSTMethod meth = (FSTMethod) selection;
				final int line = getMethodLine(file, meth);
				if (line != -1) {
					scrollToLine(activeEditor, line);
				}
			} else if (selection instanceof FSTField) {
				final FSTField field = (FSTField) selection;
				final int line = getFieldLine(file, field);
				if (line != -1) {
					scrollToLine(activeEditor, line);
				}
			} else if (selection instanceof FSTInvariant) {
				final FSTInvariant inv = (FSTInvariant) selection;
				final int line = getInvariantLine(file, inv);
				if (line != -1) {
					scrollToLine(activeEditor, line);
				}

			} else if (selection instanceof FSTClassFragment) {
				final FSTClassFragment cf = (FSTClassFragment) selection;
				final int line = getClassFragmentLine(file, cf);
				if (line != -1) {
					scrollToLine(activeEditor, line);
				}
			}

			else if (selection instanceof FSTDirective) {
				final FSTDirective directive = (FSTDirective) selection;
				scrollToLine(activeEditor, directive.getStartLine(), directive.getEndLine(), directive.getStartOffset(), directive.getEndLength());
			}
		}

	}

	// TODO refactor into FSTModel
	private int getFieldLine(IFile iFile, FSTField field) {
		for (final FSTRole r : field.getRole().getFSTClass().getRoles()) {
			if (r.getFile().equals(iFile)) {
				for (final FSTField f : r.getAllFields()) {
					if (f.compareTo(field) == 0) {
						return f.getLine();
					}
				}
			}
		}
		return -1;
	}

	// TODO refactor into FSTModel
	private int getInvariantLine(IFile iFile, FSTInvariant inv) {
		for (final FSTRole r : inv.getRole().getFSTClass().getRoles()) {
			if (r.getFile().equals(iFile)) {
				for (final FSTInvariant i : r.getClassFragment().getInvariants()) {
					if (i.compareTo(inv) == 0) {
						return i.getLine();
					}
				}
			}
		}
		return -1;
	}

	// TODO refactor into FSTModel
	private int getClassFragmentLine(IFile iFile, FSTClassFragment cf) {
		for (final FSTRole r : cf.getRole().getFSTClass().getRoles()) {
			if (r.getFile().equals(iFile)) {
				for (final FSTClassFragment i : r.getAllInnerClasses()) {
					if (i.compareTo(cf) == 0) {
						return i.getLine();
					}
				}
			}
		}
		return -1;
	}

	private int getMethodLine(IFile iFile, FSTMethod meth) {
		for (final FSTRole r : meth.getRole().getFSTClass().getRoles()) {
			if (r.getFile().equals(iFile)) {
				for (final FSTMethod m : r.getAllMethods()) {
					if (m.compareTo(meth) == 0) {
						return m.getLine();
					}
				}
			}
		}
		return -1;
	}

	/**
	 * Jumps to a line in the given editor
	 *
	 * @param editorPart
	 * @param lineNumber
	 */
	public static void scrollToLine(IEditorPart editorPart, int lineNumber) {
		if (!(editorPart instanceof ITextEditor) || (lineNumber <= 0)) {
			return;
		}
		final ITextEditor editor = (ITextEditor) editorPart;
		final IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
		if (document != null) {
			IRegion lineInfo = null;
			try {
				lineInfo = document.getLineInformation(lineNumber - 1);
			} catch (final BadLocationException e) {}
			if (lineInfo != null) {
				editor.selectAndReveal(lineInfo.getOffset(), lineInfo.getLength());
			}
		}
	}

	/**
	 * Highlights the whole if-Block for a FSTDirective
	 *
	 * @param editorPart
	 * @param startLine the first line of a directive
	 * @param endLine the last line of a directive
	 * @param startOffset characters before the statement starts
	 * @param endOffset length of the last line
	 */
	public static void scrollToLine(IEditorPart editorPart, int startLine, int endLine, int startOffset, int endOffset) {
		if (!(editorPart instanceof ITextEditor) || (startLine < 0) || (endLine < 0)) {
			return;
		}
		final ITextEditor editor = (ITextEditor) editorPart;
		final IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
		if (document != null) {
			try {
				final int offset = document.getLineOffset(startLine) + startOffset;
				editor.selectAndReveal(offset, (document.getLineOffset(endLine) - (offset)) + endOffset);
			} catch (final BadLocationException e) {}
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeViewerListener#treeCollapsed(org.eclipse.jface.viewers.TreeExpansionEvent)
	 */
	@Override
	public void treeCollapsed(TreeExpansionEvent event) {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeViewerListener#treeExpanded(org.eclipse.jface.viewers.TreeExpansionEvent)
	 */
	@Override
	public void treeExpanded(TreeExpansionEvent event) {
		// TODO Auto-generated method stub

	}
}
