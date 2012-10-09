/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.views.collaboration.editparts;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.draw2d.FigureCanvas;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Panel;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.Request;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.figures.RoleFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.RoleFigureLabel;
import de.ovgu.featureide.ui.views.collaboration.model.Role;
import de.ovgu.featureide.ui.views.collaboration.outline.CollaborationOutline;

/**
 * EditPart for Roles.
 * 
 * @author Constanze Adler
 */
public class RoleEditPart extends AbstractGraphicalEditPart {

	public RoleEditPart(Role role) {
		super();
		setModel(role);
	}

	public Role getRoleModel() {
		return (Role) getModel();
	}

	@Override
	protected IFigure createFigure() {
		return new RoleFigure(getRoleModel());
	}

	@Override
	protected void createEditPolicies() {
	}

	/**
	 * {@Link ModelEditPart#refreshVisuals()}
	 */
	@Override
	protected void refreshVisuals() {
	}

	/**
	 * opens the fields/methods/file of the role with its default editor.
	 */
	public void performRequest(Request request) {
		if (REQ_OPEN.equals(request.getType())) {
			IFile file = this.getRoleModel().getRoleFile();
			if (file == null)
				return;

			IWorkbenchPage page = getActivePage();
			if (page != null) {
				try {
					
					RoleFigure roleFigure = (RoleFigure) this.getFigure();
					if (roleFigure.isFieldMethodFilterActive() || !CorePlugin.getFeatureProject(file).getComposer().showContextFieldsAndMethods()) {
						openClickedElementInEditor(roleFigure, file);
					}
					else 
						openEditor(file);
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}
		}
		super.performRequest(request);
	}

	private IWorkbenchPage getActivePage() {
		return UIPlugin.getDefault().getWorkbench().getActiveWorkbenchWindow().getActivePage();
	}
	
	private IEditorDescriptor getDescriptor(IFile file) throws CoreException
	{
		IContentType contentType = null;
		IContentDescription description = file.getContentDescription();
		if (description != null) {
			contentType = description.getContentType();
		}
		if (contentType != null) {
			return PlatformUI.getWorkbench().getEditorRegistry()
					.getDefaultEditor(file.getName(), contentType);
		} else {
			return PlatformUI.getWorkbench().getEditorRegistry()
					.getDefaultEditor(file.getName());
		}
	}
	
	private ITextEditor openEditor(IFile file) throws CoreException
	{
		IWorkbenchPage page = getActivePage();
		if (page == null) return null;
		
		IEditorDescriptor desc = getDescriptor(file);
		
		if (desc != null) {
			return (ITextEditor) page.openEditor(new FileEditorInput(file), desc.getId());
		} else {
			// case: there is no default editor for the file
			return (ITextEditor) page.openEditor(new FileEditorInput(file),
					"org.eclipse.ui.DefaultTextEditor");
		}
	}
	
	/**
	 * search clicked element of current cursor position and open element in editor
	 */
	private void openClickedElementInEditor(RoleFigure roleFigure, IFile file) throws CoreException {
		Point point = getCursorPosition();
		List<?> panelList = roleFigure.getChildren();
		ITextEditor editor; 
		
		for (Object o : panelList) {
			Panel panel = (Panel) o;
			List<?> labelList = panel.getChildren();

			for (Object child : labelList) {
				RoleFigureLabel label = (RoleFigureLabel) child;
				Rectangle rect = label.getBounds();
				int y = rect.y;
				if (point.y >= y && point.y <= (y + rect.height)) {
					LinkedList<FSTField> fields = this.getRoleModel().fields;
					for (FSTField fstField : fields) {
						if (fstField.getName().equals(label.getElementName())) {
							editor = openEditor(file);
							if (editor != null)	CollaborationOutline.scrollToLine(editor,fstField.getLineNumber(file));
							return;
						}
					}
					
					LinkedList<FSTMethod> methods = this.getRoleModel().methods;
					for (FSTMethod fstMethod : methods) {
						if (fstMethod.getName().equals(label.getElementName())) {
							editor = openEditor(file);
							if (editor != null)	CollaborationOutline.scrollToLine(editor,fstMethod.getLineNumber(file));
							return;
						}
					}
					
					LinkedList<FSTDirective> directives = this.getRoleModel().directives;
					for (FSTDirective fstDirective : directives) {
						if (fstDirective.toDependencyString().equals(label.getElementName())) {
							editor = openEditor(file);
							if (editor != null)	CollaborationOutline.scrollToLine(editor, fstDirective.getStartLine(), fstDirective.getEndLine(), fstDirective.getStartOffset(), fstDirective.getEndLength());
							return;
						}
					}
					
					LinkedList<IFile> files = this.getRoleModel().files;
					for (IFile iFile : files) {
						if (iFile.getName().equals(label.getElementName())) {
							openEditor(iFile);
							return;
						}
					}
				}
			}
		}
		//if no element found, open file in editor
		openEditor(file);
		getViewer().getContents().refresh();
	}
	
	private Point getCursorPosition() 
	{
		Display display = Display.getDefault();
		FigureCanvas figureCanvas = (FigureCanvas)this.getViewer().getControl();
		Point point = figureCanvas.toControl(display.getCursorLocation());
		
		org.eclipse.draw2d.geometry.Point location = figureCanvas.getViewport().getViewLocation();
		
		int x = point.x + location.x;
		int y = point.y + location.y;
		if (point.x < 0) x += figureCanvas.getViewport().getBounds().width;
		if (point.y < 0) y += figureCanvas.getViewport().getBounds().height;
		
		return new Point(x,y);
	}
}
