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
package de.ovgu.featureide.ui.views.collaboration.outline;

import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_CONTEXT_OUTLINE;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractClassFragment;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;

/**
 * Provides labels and images for Collaboration outline
 *
 * @author Sebastian Krieter
 */
public class ContextOutlineLabelProvider extends OutlineLabelProvider {

	@Override
	public void addListener(ILabelProviderListener listener) {}

	@Override
	public void dispose() {}

	@Override
	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {}

	@Override
	public Image getImage(Object element) {
		if (element instanceof AbstractClassFragment) {
			return GUIDefaults.IMAGE_CLASS;
		} else if (element instanceof AbstractMethodSignature) {
			// TODO MPL: constructor icon
			switch (((AbstractMethodSignature) element).getVisibilty()) {
			case AbstractSignature.VISIBILITY_DEFAULT:
				return GUIDefaults.IMAGE_METHODE_DEFAULT;
			case AbstractSignature.VISIBILITY_PRIVATE:
				return GUIDefaults.IMAGE_METHODE_PRIVATE;
			case AbstractSignature.VISIBILITY_PROTECTED:
				return GUIDefaults.IMAGE_METHODE_PROTECTED;
			case AbstractSignature.VISIBILITY_PUBLIC:
				return GUIDefaults.IMAGE_METHODE_PUBLIC;
			}
		} else if (element instanceof AbstractFieldSignature) {
			switch (((AbstractFieldSignature) element).getVisibilty()) {
			case AbstractSignature.VISIBILITY_DEFAULT:
				return GUIDefaults.IMAGE_FIELD_DEFAULT;
			case AbstractSignature.VISIBILITY_PRIVATE:
				return GUIDefaults.IMAGE_FIELD_PRIVATE;
			case AbstractSignature.VISIBILITY_PROTECTED:
				return GUIDefaults.IMAGE_FIELD_PROTECTED;
			case AbstractSignature.VISIBILITY_PUBLIC:
				return GUIDefaults.IMAGE_FIELD_PUBLIC;
			}
		} else if (element instanceof AbstractClassSignature) {
			return GUIDefaults.IMAGE_CLASS;
		}
		return null;
	}

	@Override
	public String getText(Object element) {
		if (element instanceof AbstractClassFragment) {
			return ((AbstractClassFragment) element).getSignature().getName();
		} else if (element instanceof AbstractSignature) {
			if (element instanceof AbstractMethodSignature) {
				final AbstractMethodSignature method = (AbstractMethodSignature) element;
				final StringBuilder sb = new StringBuilder();
				sb.append(method.getName());
				sb.append('(');
				for (final String parameterType : method.getParameterTypes()) {
					sb.append(parameterType);
					sb.append(", ");
				}
				if (method.getParameterTypes().size() > 0) {
					sb.delete(sb.length() - 2, sb.length());
				}
				sb.append(')');
				if (!method.isConstructor()) {
					sb.append(" : ");
					sb.append(method.getType());
				}
				return sb.toString();
			} else if (element instanceof AbstractFieldSignature) {
				final AbstractFieldSignature field = (AbstractFieldSignature) element;
				return field.getName() + " : " + field.getType();
			} else if (element instanceof AbstractClassSignature) {
				return ((AbstractClassSignature) element).getName();
			}
		} else if (element instanceof IFeature) {
			return ((IFeature) element).getProperty().getDisplayName();
		}
		return element.toString();
	}

	@Override
	public void colorizeItems(TreeItem[] treeItems, IFile file) {}

	@Override
	public void setForeground(TreeItem item, IFile file) {
		item.setForeground(item.getDisplay().getSystemColor(SWT.COLOR_GRAY));
	}

	@Override
	public String getLabelProvName() {
		return FEATURE_CONTEXT_OUTLINE;
	}

	@Override
	public int getOutlineType() {
		return OutlineLabelProvider.OUTLINE_CODE;
	}

	@Override
	public boolean refreshContent(IFile oldFile, IFile currentFile) {
		return false;
	}

	@Override
	public void init() {
		// viewer.addSelectionChangedListener(sListner);
	}

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

	private final ISelectionChangedListener sListner = new ISelectionChangedListener() {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			if (viewer.getInput() != null) {
				final Object selection = ((IStructuredSelection) viewer.getSelection()).getFirstElement();
				if (!(viewer.getInput() instanceof IResource)) {
					return;
				}
				final IFeatureProject featureProject = CorePlugin.getFeatureProject((IResource) viewer.getInput());
				if (featureProject != null) {
					if (selection instanceof AbstractClassFragment) {
						final AbstractSignature sig = ((AbstractClassFragment) selection).getSignature();
						final AFeatureData[] featureDataArray = sig.getFeatureData();
						openEditor(sig, featureProject, featureDataArray[0].getID());
					} else if (selection instanceof AbstractSignature) {
						final AbstractSignature sig = (AbstractSignature) selection;
						final AFeatureData[] featureDataArray = sig.getFeatureData();
						openEditor(sig, featureProject, featureDataArray[0].getID());
					} else if (selection instanceof IFeature) {
						final ProjectSignatures signatures = featureProject.getProjectSignatures();
						if (signatures != null) {
							final TreeItem decl = viewer.getTree().getSelection()[0].getParentItem();
							openEditor((AbstractSignature) decl.getData(), featureProject, signatures.getFeatureID(((IFeature) selection).getName()));
						}
					}
				}
			}
		}

		private void openEditor(AbstractSignature sig, IFeatureProject featureProject, int featureID) {
			final FSTModel model = featureProject.getFSTModel();
			final ProjectSignatures signatures = featureProject.getProjectSignatures();
			if ((model != null) && (signatures != null)) {
				AbstractSignature parent = sig;
				while (parent.getParent() != null) {
					parent = parent.getParent();
				}

				final String fullName = parent.getFullName();
				final String fileName = (fullName.startsWith(".")) ? fullName.substring(1) : fullName.replace('.', '/');

				final IFile iFile = model.getFeature(signatures.getFeatureName(featureID)).getRole(fileName + ".java").getFile();

				if (iFile.isAccessible()) {
					final IWorkbench workbench = PlatformUI.getWorkbench();
					try {
						final IContentDescription description = iFile.getContentDescription();
						final IEditorDescriptor desc =
							workbench.getEditorRegistry().getDefaultEditor(iFile.getName(), (description != null) ? description.getContentType() : null);
						final IWorkbenchPage activePage = workbench.getActiveWorkbenchWindow().getActivePage();
						IEditorPart editorPart = activePage.findEditor(new FileEditorInput(iFile));
						if (editorPart == null) {
							editorPart = activePage.openEditor(new FileEditorInput(iFile), (desc != null) ? desc.getId() : "org.eclipse.ui.DefaultTextEditor");
						}
						final int dataIndex = sig.hasFeature(featureID);
						scrollToLine(editorPart, (dataIndex > -1) ? sig.getFeatureData()[dataIndex].getStartLineNumber() : 1);
					} catch (final CoreException e) {
						UIPlugin.getDefault().logError(e);
					}
				}
			}
		}
	};

}
