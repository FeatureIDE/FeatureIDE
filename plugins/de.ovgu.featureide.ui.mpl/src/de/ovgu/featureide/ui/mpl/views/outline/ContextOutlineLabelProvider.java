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
package de.ovgu.featureide.ui.mpl.views.outline;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractFieldSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractMethodSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.collaboration.outline.OutlineLabelProvider;

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
			//TODO MPL: constructor icon
			switch (((AbstractMethodSignature) element).getVisibilty()) {
			case AbstractSignature.VISIBILITY_DEFAULT: return GUIDefaults.IMAGE_METHODE_DEFAULT;
			case AbstractSignature.VISIBILITY_PRIVATE: return GUIDefaults.IMAGE_METHODE_PRIVATE;
			case AbstractSignature.VISIBILITY_PROTECTED: return GUIDefaults.IMAGE_METHODE_PROTECTED;
			case AbstractSignature.VISIBILITY_PUBLIC: return GUIDefaults.IMAGE_METHODE_PUBLIC;
			}
		} else if (element instanceof AbstractFieldSignature) {
			switch (((AbstractFieldSignature) element).getVisibilty()) {
			case AbstractSignature.VISIBILITY_DEFAULT: return GUIDefaults.IMAGE_FIELD_DEFAULT;
			case AbstractSignature.VISIBILITY_PRIVATE: return GUIDefaults.IMAGE_FIELD_PRIVATE;
			case AbstractSignature.VISIBILITY_PROTECTED: return GUIDefaults.IMAGE_FIELD_PROTECTED;
			case AbstractSignature.VISIBILITY_PUBLIC: return GUIDefaults.IMAGE_FIELD_PUBLIC;
			}
		} else if (element instanceof AbstractClassSignature) {
			return GUIDefaults.IMAGE_CLASS;
		}
		return null;
	}

	@Override
	public String getText(Object element) {
		if (element instanceof  AbstractClassFragment) {
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
//		for (int i = 0; i < treeItems.length; i++) {
//			
//			if (treeItems[i].getData() instanceof AbstractClassFragment) {
//				treeItems[i].setForeground(treeItems[i].getDisplay()
//						.getSystemColor(SWT.DEFAULT));
//				setForeground(treeItems[i], null);
//			} else{ //if (treeItems[i].getData() instanceof FSTRole) {
//				
//					// get old Font and simply make it bold
////					treeItems[i].setFont(new Font(treeItems[i].getDisplay(),
////									treeItems[i].getFont().getFontData()[0]
////											.getName(), treeItems[i].getFont()
////											.getFontData()[0].getHeight(),
////									SWT.BOLD));
////					
////					treeItems[i].setForeground(treeItems[i].getDisplay()
////							.getSystemColor(SWT.DEFAULT));
//			}
//			if (treeItems[i].getItems().length > 0) {
//				colorizeItems(treeItems[i].getItems(), file);
//			}
//		}
	}
	
	@Override
	public void setForeground(TreeItem item, IFile file) {
		item.setForeground(item.getDisplay().getSystemColor(SWT.COLOR_GRAY));
	}
	
	@Override
	public String getLabelProvName(){
		return "Feature Context Outline";
	}

	@Override
	public int getOutlineType() {
		return OutlineLabelProvider.OUTLINE_CODE;
	}

	@Override
	public boolean refreshContent(TreeItem[] items, IFile oldFile, IFile currentFile) {
		return false;
	}

	@Override
	public void init() {
		viewer.addSelectionChangedListener(sListner);
	}
	
	ISelectionChangedListener sListner = new ISelectionChangedListener() {
		
		// TODO refactor into FSTModel
		private int getFieldLine(IFile iFile, FSTField field) {
			for (FSTRole r : field.getRole().getFSTClass().getRoles()) {
				if (r.getFile().equals(iFile)) {
					for (FSTField f : r.getFields()) {
						if (f.comparesTo(field)) {
							return f.getLine();
						}
					}
				}
			}
			return -1;
		}

		private int getMethodLine(IFile iFile, FSTMethod meth) {
			for (FSTRole r : meth.getRole().getFSTClass().getRoles()) {
				if (r.getFile().equals(iFile)) {
					for (FSTMethod m : r.getMethods()) {
						if (m.comparesTo(meth)) {
							return m.getLine();
						}
					}
				}
			}
			return -1;
		}
		
		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			if (viewer.getInput() != null) {
				Object selection = ((IStructuredSelection) viewer.getSelection()).getFirstElement();
				System.out.println();
				
				if(selection instanceof AbstractSignature){
					AbstractSignature ms = (AbstractSignature) selection;
					int i = ms.getLine();
					MessageDialog.openConfirm(null, "Line", "" + i);
					System.out.println();
				}
				
				
				
//				if (selection instanceof FSTMethod) {
//					FSTMethod meth = (FSTMethod) selection;
//					int line = getMethodLine(iFile, meth);
//					if (line != -1) {
//						scrollToLine(active_editor, line);
//					}
//				} else if (selection instanceof FSTField) {
//					FSTField field = (FSTField) selection;
//					int line = getFieldLine(iFile, field);
//					if (line != -1) {
//						scrollToLine(active_editor, line);
//					}
//				}
				
				
				
//				} else if (selection instanceof FSTDirective) {
//					FSTDirective directive = (FSTDirective) selection;
//					scrollToLine(active_editor, directive.getStartLine(), directive.getEndLine(), 
//							directive.getStartOffset(), directive.getEndLength());
//				} else if (selection instanceof FSTRole) {
//					FSTRole r = (FSTRole) selection;
//					if (r.getFile().isAccessible()) {
//						IWorkbench workbench = PlatformUI
//								.getWorkbench();
//						IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
//						IWorkbenchPage page = window.getActivePage();
//						IContentType contentType = null;
//						try {
//							iFile = r.getFile();
//							IContentDescription description = iFile
//									.getContentDescription();
//							if (description != null) {
//								contentType = description.getContentType();
//							}
//							IEditorDescriptor desc = null;
//							if (contentType != null) {
//								desc = workbench.getEditorRegistry()
//										.getDefaultEditor(iFile.getName(), contentType);
//							} else {
//								desc = workbench.getEditorRegistry()
//										.getDefaultEditor(iFile.getName());
//							}
//							if (desc != null) {
//								page.openEditor(new FileEditorInput(iFile),
//										desc.getId());
//							} else {
//								// case: there is no default editor for the file
//								page.openEditor(new FileEditorInput(iFile),
//										"org.eclipse.ui.DefaultTextEditor");
//							}
//						} catch (CoreException e) {
//							UIPlugin.getDefault().logError(e);
//						}
//					}
//				}
			}
			
		}
	};

}
