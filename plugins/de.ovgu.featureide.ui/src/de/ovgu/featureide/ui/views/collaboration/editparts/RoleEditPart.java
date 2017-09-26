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
package de.ovgu.featureide.ui.views.collaboration.editparts;

import java.util.Collection;
import java.util.List;
import java.util.TreeSet;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.draw2d.FigureCanvas;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Panel;
import org.eclipse.draw2d.Viewport;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.gef.Request;
import org.eclipse.gef.editparts.AbstractGraphicalEditPart;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.figures.RoleFigure;
import de.ovgu.featureide.ui.views.collaboration.figures.RoleFigureLabel;

/**
 * EditPart for Roles.
 *
 * @author Constanze Adler
 */
public class RoleEditPart extends AbstractGraphicalEditPart {

	public RoleEditPart(FSTRole role) {
		super();
		setModel(role);
	}

	public FSTRole getRoleModel() {
		return (FSTRole) getModel();
	}

	@Override
	protected IFigure createFigure() {
		return new RoleFigure(getRoleModel());
	}

	@Override
	protected void createEditPolicies() {}

	/**
	 * {@Link ModelEditPart#refreshVisuals()}
	 */
	@Override
	protected void refreshVisuals() {}

	/**
	 * opens the fields/methods/file of the role with its default editor.
	 */
	@Override
	public void performRequest(Request request) {
		if (REQ_OPEN.equals(request.getType())) {
			final IFile file = getRoleModel().getFile();
			if (file == null) {
				return;
			}

			final IWorkbenchPage page = getActivePage();
			if (page != null) {
				try {

					final RoleFigure roleFigure = (RoleFigure) getFigure();
					if (roleFigure.isFieldMethodFilterActive() || !CorePlugin.getFeatureProject(file).getComposer().showContextFieldsAndMethods()) {
						openElement(roleFigure, file);
					} else {
						openEditor(file);
					}
				} catch (final CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}
		}
		super.performRequest(request);
	}

	private IWorkbenchPage getActivePage() {
		return UIPlugin.getDefault().getWorkbench().getActiveWorkbenchWindow().getActivePage();
	}

	private IEditorDescriptor getDescriptor(IFile file) throws CoreException {
		IContentType contentType = null;
		final IContentDescription description = file.getContentDescription();
		if (description != null) {
			contentType = description.getContentType();
		}
		if (contentType != null) {
			return PlatformUI.getWorkbench().getEditorRegistry().getDefaultEditor(file.getName(), contentType);
		} else {
			return PlatformUI.getWorkbench().getEditorRegistry().getDefaultEditor(file.getName());
		}
	}

	private ITextEditor openEditor(IFile file) throws CoreException {
		final IWorkbenchPage page = getActivePage();
		if (page == null) {
			return null;
		}

		final IEditorDescriptor desc = getDescriptor(file);

		if (desc != null) {
			return (ITextEditor) page.openEditor(new FileEditorInput(file), desc.getId());
		} else {
			// case: there is no default editor for the file
			return (ITextEditor) page.openEditor(new FileEditorInput(file), "org.eclipse.ui.DefaultTextEditor");
		}
	}

	/**
	 * search clicked element of current cursor position and open element in editor
	 */
	private void openElement(RoleFigure roleFigure, IFile file) throws CoreException {
		final Point point = getCursorPosition();
		final List<?> panelList = roleFigure.getChildren();
		ITextEditor editor;

		for (final Object o : panelList) {
			final Panel panel = (Panel) o;
			final List<?> labelList = panel.getChildren();

			for (final Object child : labelList) {
				final RoleFigureLabel label = (RoleFigureLabel) child;
				final Rectangle rect = label.getBounds();
				final int y = rect.y;
				if ((point.y >= y) && (point.y <= (y + rect.height))) {

					final TreeSet<FSTInvariant> invariants = getRoleModel().getClassFragment().getInvariants();
					for (final FSTInvariant invariant : invariants) {
						if (invariant.getFullName().equals(label.getElementName())) {
							editor = openEditor(file);
							if (editor != null) {
								scrollToLine(editor, invariant.getLine());
							}
							return;
						}

					}
					final Collection<FSTField> fields = getRoleModel().getAllFields();

					for (final FSTField fstField : fields) {
						if (fstField.getFullName().equals(label.getElementName())) {
							editor = openEditor(file);
							if (editor != null) {
								scrollToLine(editor, fstField.getLine());
							}
							return;
						}
					}

					final Collection<FSTClassFragment> innerClasses = getRoleModel().getAllInnerClasses();
					for (final FSTClassFragment fstInnerClass : innerClasses) {
						if (fstInnerClass.getFullName().equals(label.getElementName())) {
							editor = openEditor(file);
							if (editor != null) {
								scrollToLine(editor, fstInnerClass.getLine());
							}
							return;
						}
					}
					final Collection<FSTMethod> methods = getRoleModel().getAllMethods();

					for (final FSTMethod fstMethod : methods) {
						if (fstMethod.getFullName().equals(label.getElementName())) {
							editor = openEditor(file);
							if (editor != null) {
								scrollToLine(editor, fstMethod.getLine());
							}
							return;
						}
					}

					final TreeSet<FSTDirective> directives = getRoleModel().getDirectives();
					for (final FSTDirective fstDirective : directives) {
						final RoleElement<?> roleElement = label.getRoleElement();
						if (fstDirective.equals(roleElement)) {
							editor = openEditor(file);
							if (editor != null) {
								scrollToLine(editor, fstDirective.getStartLine(), fstDirective.getEndLine(), fstDirective.getStartOffset(),
										fstDirective.getEndLength());
							}
							return;
						}
					}
				}
			}
		}
		// if no element found, open file in editor
		openEditor(file);
		getViewer().getContents().refresh();
	}

	private Point getCursorPosition() {
		final Display display = Display.getDefault();
		final FigureCanvas figureCanvas = (FigureCanvas) getViewer().getControl();
		final Point point = figureCanvas.toControl(display.getCursorLocation());

		final Viewport viewport = figureCanvas.getViewport();
		final org.eclipse.draw2d.geometry.Point location = viewport.getViewLocation();

		int x = point.x + location.x;
		int y = point.y + location.y;
		final Rectangle bounds = viewport.getBounds();
		if (point.x < 0) {
			x += bounds.width;
		}
		if (point.y < 0) {
			y += bounds.height;
		}

		return new Point(x, y);
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
}
