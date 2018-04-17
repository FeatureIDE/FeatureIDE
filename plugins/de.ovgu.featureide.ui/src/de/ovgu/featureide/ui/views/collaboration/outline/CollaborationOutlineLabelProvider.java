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

import static de.ovgu.featureide.fm.core.localization.StringTable.CLASS_IS_NULL;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFAULT_OUTLINE;
import static de.ovgu.featureide.fm.core.localization.StringTable.FILE_IS_NULL;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.fstmodel.FSTAsmetaLDomain;
import de.ovgu.featureide.core.fstmodel.FSTAsmetaLInitialization;
import de.ovgu.featureide.core.fstmodel.FSTAstemaLFunction;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTContractedRole;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.IRoleElement;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;

/**
 * Provides labels and images for Collaboration outline
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Dominic Labsch
 * @author Daniel P�sche
 */
public class CollaborationOutlineLabelProvider extends OutlineLabelProvider implements GUIDefaults {

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
		if (element instanceof FSTClassFragment) {
			return IMAGE_CLASS;
		}
		if (element instanceof IRoleElement) {
			final IRoleElement fstModelElement = (IRoleElement) element;
			if (fstModelElement instanceof FSTAsmetaLDomain) {
				return IMAGE_FIELD_PUBLIC;
			} else if (fstModelElement instanceof FSTAstemaLFunction) {
				return IMAGE_FIELD_PRIVATE;
			} else if (fstModelElement instanceof FSTAsmetaLInitialization) {
				return IMAGE_METHODE_PROTECTED;
			} else if (fstModelElement instanceof FSTField) {
				final FSTField field = (FSTField) fstModelElement;
				final String fileExtension = field.getFile().getFileExtension();
				if ("java".equals(fileExtension) || "jak".equals(fileExtension) || "cs".equals(fileExtension)) {
					if (field.isPrivate()) {
						return IMAGE_FIELD_PRIVATE;
					} else if (field.isProtected()) {
						return IMAGE_FIELD_PROTECTED;
					} else if (field.isPublic()) {
						return IMAGE_FIELD_PUBLIC;
					} else {
						return IMAGE_FIELD_DEFAULT;
					}
				} else if ("hs".equals(fileExtension)) {
					return IMAGE_HASKELL_TYPE;
				} else if ("h".equals(fileExtension) || "c".equals(fileExtension)) {
					return IMAGE_FIELD_DEFAULT;
				}

			} else if (fstModelElement instanceof FSTInvariant) {
				return IMAGE_AT_WITHOUT_WHITE_BACKGROUND;
			} else if (fstModelElement instanceof FSTMethod) {
				final FSTMethod method = (FSTMethod) fstModelElement;

				final String fileExtension = method.getFile().getFileExtension();
				if ("java".equals(fileExtension) || "jak".equals(fileExtension) || "cs".equals(fileExtension)) {

					if (method.hasContract() || method.contractsInRefinements()) {
						if (method.isPrivate()) {
							return IMAGE_METHODE_PRIVATE_CONTRACT;
						} else if (method.isProtected()) {
							return IMAGE_METHODE_PROTECTED_CONTRACT;
						} else if (method.isPublic()) {
							return IMAGE_METHODE_PUBLIC_CONTRACT;
						} else {
							return IMAGE_METHODE_DEFAULT_CONTRACT;
						}
					} else {
						if (method.isPrivate()) {
							return IMAGE_METHODE_PRIVATE;
						} else if (method.isProtected()) {
							return IMAGE_METHODE_PROTECTED;
						} else if (method.isPublic()) {
							return IMAGE_METHODE_PUBLIC;
						} else {
							return IMAGE_METHODE_DEFAULT;
						}
					}
				} else if ("hs".equals(fileExtension)) {
					return IMAGE_HASKELL_LAMBDA;
				} else if ("h".equals(fileExtension) || "c".equals(fileExtension)) {
					return IMAGE_METHODE_DEFAULT;
				}
			}
		} else if (element instanceof FSTClass) {

			final FSTClass datClass = (FSTClass) element;
			final String className = datClass.getName();
			final int extIndex = className.lastIndexOf('.');
			if (extIndex > -1) {
				final String fileExtension = className.substring(extIndex + 1);
				if ("java".equals(fileExtension) || "jak".equals(fileExtension) || "cs".equals(fileExtension) || "h".equals(fileExtension)
					|| "c".equals(fileExtension)) {
					return IMAGE_CLASS;
				} else if ("hs".equals(fileExtension)) {
					return IMAGE_HASKELL_MODULE;
				}
			}
		} else if (element instanceof FSTContractedRole) {
			return IMAGE_AT_WITHOUT_WHITE_BACKGROUND;
		}
		return null;
	}

	@Override
	public String getText(Object element) {
		if (element instanceof FSTClass) {
			final FSTClass fstclass = (FSTClass) element;
			String toAppend = "";
			for (final FSTRole r : fstclass.getRoles()) {
				if (!r.getDirectives().isEmpty()) {
					return fstclass.getName();
				}
				if ((viewer != null) && (viewer.getInput() != null) && r.getFile().equals(viewer.getInput())) {
					toAppend = " - " + r.getFeature().getName();
				}
			}
			return fstclass.getName() + toAppend;
		}

		if (element instanceof FSTMethod) {
			return ((FSTMethod) element).getFullName();
		}

		if (element instanceof FSTInvariant) {
			return ((FSTInvariant) element).getFullName();
		}

		if (element instanceof FSTField) {
			return ((FSTField) element).getFullName();
		}

		if (element instanceof FSTFeature) {
			return ((FSTFeature) element).getName();
		}

		if (element instanceof FSTRole) {
			return ((FSTRole) element).getFeature().getName();
		}

		if (element instanceof FSTDirective) {
			return ((FSTDirective) element).toString();
		}

		if (element instanceof String) {
			return (String) element;
		}

		if (element instanceof FSTClassFragment) {
			return ((FSTClassFragment) element).getName();
		}

		return "";

	}

	@Override
	public String getLabelProvName() {
		return DEFAULT_OUTLINE;
	}

	@Override
	public int getOutlineType() {
		return OutlineLabelProvider.OUTLINE_CODE;
	}

	@Override
	public void colorizeItems(TreeItem[] treeItems, IFile file) {
		for (int i = 0; i < treeItems.length; i++) {
			if (treeItems[i].getData() instanceof IRoleElement) {
				setForeground(treeItems[i], file);
			}
			if (treeItems[i].getData() instanceof FSTRole) {
				if (((FSTRole) treeItems[i].getData()).getFile().equals(file)) {
					// get old Font and simply make it bold
					treeItems[i].setFont(new Font(treeItems[i].getDisplay(), treeItems[i].getFont().getFontData()[0].getName(),
							treeItems[i].getFont().getFontData()[0].getHeight(), SWT.BOLD));
				} else {
					treeItems[i].setFont(new Font(treeItems[i].getDisplay(), treeItems[i].getFont().getFontData()[0].getName(),
							treeItems[i].getFont().getFontData()[0].getHeight(), SWT.NORMAL));
				}
				setForeground(treeItems[i], file);
			}
			if (treeItems[i].getItems().length > 0) {
				colorizeItems(treeItems[i].getItems(), file);
			}
		}
	}

	/**
	 * @return <code>true</code> if the new input does not change the old content.
	 */
	private boolean hasSameClass(FSTClass Class, IFile oldFile, IFile currentFile) {
		if (Class == null) {
			UIPlugin.getDefault().logWarning(CLASS_IS_NULL);
			return false;
		}
		if (currentFile == null) {
			UIPlugin.getDefault().logWarning(FILE_IS_NULL);
			return false;
		}
		if (!currentFile.getProject().equals(oldFile.getProject())) {
			return false;
		}
		if (isBuildFile(currentFile.getParent(), CorePlugin.getFeatureProject(currentFile).getBuildFolder())) {
			return true;
		}
		if (isBuildFile(oldFile.getParent(), CorePlugin.getFeatureProject(oldFile).getBuildFolder())) {
			return true;
		}

		if (currentFile.equals(oldFile)) {
			return true;
		}
		boolean i = false;
		boolean j = false;
		for (final FSTRole role : Class.getRoles()) {
			if (role.getFile().equals(oldFile)) {
				i = true;
			} else if (role.getFile().equals(currentFile)) {
				j = true;
			}
		}
		return j && i;
	}

	/**
	 * @param parent
	 * @param buildFolder
	 * @return <code>true</code> if the build folder contains the given folder
	 */
	private boolean isBuildFile(IContainer parent, IFolder buildFolder) {
		if (parent == null) {
			return false;
		}
		if (parent instanceof IFolder) {
			if (parent.equals(buildFolder)) {
				return true;
			}
			return isBuildFile(parent.getParent(), buildFolder);
		}
		return false;
	}

	@Override
	public void setForeground(TreeItem item, IFile iFile) {
		final Object data = item.getData();
		if (data instanceof FSTDirective) {
			item.setForeground(viewer.getControl().getDisplay().getSystemColor(SWT.DEFAULT));
			final int colorID = ((FSTDirective) data).getColor();
			if (colorID != FeatureColor.NO_COLOR.getValue()) {
				item.setBackground(new Color(null, ColorPalette.getRGB(colorID, 0.5f)));
			} else {
				item.setBackground(null);
			}
		} else if (data instanceof FSTRole) {
			final int colorID = ((FSTRole) data).getFeature().getColor();
			if (colorID != FeatureColor.NO_COLOR.getValue()) {
				item.setBackground(new Color(null, ColorPalette.getRGB(colorID, 0.5f)));
			} else {
				item.setBackground(null);
			}
		} else {
			final IRoleElement element = (IRoleElement) data;
			for (final FSTRole role : element.getRole().getFSTClass().getRoles()) {
				if (role.getFile().equals(iFile)
					&& (((element instanceof FSTMethod) && role.getAllMethods().contains(element) && role.getClassFragment().getMethods().contains(element))
						|| ((element instanceof FSTInvariant) && role.getClassFragment().getInvariants().contains(element))
						|| ((element instanceof FSTField) && role.getAllFields().contains(element) && role.getClassFragment().getFields().contains(element))
						|| ((element instanceof FSTClassFragment) && role.getAllInnerClasses().contains(element)))) {
					item.setForeground(viewer.getControl().getDisplay().getSystemColor(SWT.DEFAULT));
					return;
				}
			}
			item.setForeground(viewer.getControl().getDisplay().getSystemColor(SWT.COLOR_GRAY));

		}
	}

	@Override
	public boolean refreshContent(IFile oldFile, IFile currentFile) {
		if ((currentFile != null) && (oldFile != null)) {
			/** only set the colors of the tree if the content is the same **/
			final TreeItem[] items = viewer.getTree().getItems();
			if (currentFile.getName().equals(oldFile.getName()) && (items.length > 0)) {
				final TreeItem item = items[0];
				if (item != null) {
					if (item.getData() instanceof FSTClass) {
						if (!hasSameClass((FSTClass) item.getData(), oldFile, currentFile)) {
							return false;
						}
						oldFile = currentFile;
						String toAppend = " - Composed class";
						for (final FSTRole r : ((FSTClass) item.getData()).getRoles()) {
							if (!r.getDirectives().isEmpty()) {
								toAppend = "";
								break;
							}
							if (r.getFile().equals(oldFile)) {
								toAppend = " - " + r.getFeature().getName();
								break;
							}
						}
						item.setText(((FSTClass) item.getData()).getName() + toAppend);
						colorizeItems(items, oldFile);
						return true;
					}
				}
			}
		}
		return false;
	}

	@Override
	public void init() {}
}
