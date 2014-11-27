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
package de.ovgu.featureide.ui.views.outline;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
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
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.signature.abstr.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.abstr.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.abstr.AbstractSignature;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.outline.OutlineLabelProvider;

/**
 * Provides labels and images for Collaboration outline
 * 
 * @author Sebastian Krieter
 */
public class ContextOutlineLabelProvider extends OutlineLabelProvider {

	@Override
	public void addListener(ILabelProviderListener listener) {
	}

	@Override
	public void dispose() {
	}

	@Override
	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {
	}

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
		} else if (element instanceof AbstractMethodSignature) {
			AbstractMethodSignature method = (AbstractMethodSignature) element;
			StringBuilder sb = new StringBuilder();
			sb.append(method.getName());
			sb.append('(');
			for (String parameterType : method.getParameterTypes()) {
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
			AbstractFieldSignature field = (AbstractFieldSignature) element;
			return field.getName() + " : " + field.getType();
		} else if (element instanceof AbstractClassSignature) {
			return ((AbstractClassSignature) element).getName();
		}
		return element.toString();
	}

	@Override
	public void colorizeItems(TreeItem[] treeItems, IFile file) {
	}

	@Override
	public void setForeground(TreeItem item, IFile file) {
		item.setForeground(item.getDisplay().getSystemColor(SWT.COLOR_GRAY));
	}

	@Override
	public String getLabelProvName() {
		return "Feature Context Outline";
	}

	@Override
	public int getOutlineType() {
		return OutlineLabelProvider.OUTLINE_CODE;
	}

	@Override
	public boolean refreshContent(IFile oldFile, IFile currentFile) {
		if (currentFile != null && oldFile != null) {
			// TODO MPL: ... ?
			if (currentFile.getName().equals(oldFile.getName()) && viewer.getTree().getItems().length > 1) {
				return true;
			}
		}
		return false;
	}

	@Override
	public void init() {
		viewer.addSelectionChangedListener(sListner);
		// viewer.setAutoExpandLevel(AbstractTreeViewer.ALL_LEVELS);
	}

	public static void scrollToLine(IEditorPart editorPart, int lineNumber) {
		if (!(editorPart instanceof ITextEditor) || lineNumber <= 0) {
			return;
		}
		ITextEditor editor = (ITextEditor) editorPart;
		IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
		if (document != null) {
			IRegion lineInfo = null;
			try {
				lineInfo = document.getLineInformation(lineNumber - 1);
			} catch (BadLocationException e) {
			}
			if (lineInfo != null) {
				editor.selectAndReveal(lineInfo.getOffset(), lineInfo.getLength());
			}
		}
	}

	private ISelectionChangedListener sListner = new ISelectionChangedListener() {
		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			if (viewer.getInput() != null) {
				Object selection = ((IStructuredSelection) viewer.getSelection()).getFirstElement();
				if (!(viewer.getInput() instanceof IResource)) {
					return;
				}
				IFeatureProject featureProject = CorePlugin.getFeatureProject((IResource) viewer.getInput());
				if (selection instanceof AbstractClassFragment) {
					final AbstractSignature sig = ((AbstractClassFragment) selection).getSignature();
					openEditor(sig, featureProject, sig.getFeatureData()[0].getId());
				} else if (selection instanceof AbstractSignature) {
					final AbstractSignature sig = (AbstractSignature) selection;
					openEditor(sig, featureProject, sig.getFeatureData()[0].getId());
				} else if (selection instanceof Feature) {
					final ProjectSignatures signatures = featureProject.getProjectSignatures();
					if (signatures != null) {
						final TreeItem decl = viewer.getTree().getSelection()[0].getParentItem();
						openEditor((AbstractSignature) decl.getData(), featureProject, signatures.getFeatureID(((Feature) selection).getName()));
					}
				}
			}
		}

		private void openEditor(AbstractSignature sig, IFeatureProject featureProject, int featureID) {
			final FSTModel model = featureProject.getFSTModel();
			final ProjectSignatures signatures = featureProject.getProjectSignatures();
			if (model != null && signatures != null) {
				AbstractSignature parent = sig;
				while (parent.getParent() != null) {
					parent = parent.getParent();
				}
				IFile iFile = model.getFeature(signatures.getFeatureName(featureID)).getRole(parent.getName() + ".java").getFile();

				if (iFile.isAccessible()) {
					IWorkbench workbench = PlatformUI.getWorkbench();
					try {
						IContentType contentType = null;
						IContentDescription description = iFile.getContentDescription();
						if (description != null) {
							contentType = description.getContentType();
						}
						IEditorDescriptor desc = workbench.getEditorRegistry().getDefaultEditor(iFile.getName(), contentType);
						IEditorPart editorPart = workbench.getActiveWorkbenchWindow().getActivePage().openEditor(new FileEditorInput(iFile), (desc != null) ? desc.getId() : "org.eclipse.ui.DefaultTextEditor");

						int linenumber = sig.getFeatureData()[sig.hasFeature(featureID)].getLineNumber();
						scrollToLine(editorPart, linenumber);
					} catch (CoreException e) {
						UIPlugin.getDefault().logError(e);
					}
				}
			}
		}
	};

}
