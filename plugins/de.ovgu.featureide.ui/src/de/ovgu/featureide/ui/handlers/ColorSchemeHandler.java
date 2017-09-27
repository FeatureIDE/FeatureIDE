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
package de.ovgu.featureide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.IAnnotationModelExtension;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors.SetFeatureColorAction;
import de.ovgu.featureide.ui.editors.annotation.ColorAnnotationModel;

/**
 * Opens a new SetFeatureColorDialog for the Feature which is at the current cursor line
 *
 * @author Paul Maximilian Bittner
 * @author Niklas Lehnfeld
 */
public class ColorSchemeHandler extends AbstractHandler {

	/*
	 * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
	 */

	private IEditorPart editorPart;
	private IDocumentProvider provider;
	private ITextEditor editor;

	@Override
	public Object execute(ExecutionEvent event) throws ExecutionException {

		editorPart = HandlerUtil.getActiveEditor(event);
		// Cast is necessary, don't remove
		editor = (ITextEditor) editorPart.getAdapter(ITextEditor.class);
		provider = editor.getDocumentProvider();

		final int line = getCursorPos();

		ColorAnnotationModel colormodel = null;
		final IEditorInput input = editor.getEditorInput();
		if ((provider != null) && (input instanceof FileEditorInput)) {
			final IAnnotationModel model = provider.getAnnotationModel(input);

			if (model instanceof IAnnotationModelExtension) {
				final IAnnotationModelExtension modelex = (IAnnotationModelExtension) model;
				colormodel = (ColorAnnotationModel) modelex.getAnnotationModel(ColorAnnotationModel.KEY);
			}
		}

		if (colormodel != null) {
			final IFeature feature = colormodel.getFeature(line);
			if (feature == null) {
				return true;
			}
			final IStructuredSelection structuredSelection = new StructuredSelection(feature);
			final SetFeatureColorAction sfca = new SetFeatureColorAction(structuredSelection, colormodel.getFeatureModel());
			sfca.run();
			return true;
		}
		return null;
	}

	private int getCursorPos() {
		final IDocument document = provider.getDocument(editorPart.getEditorInput());
		final ITextSelection textSelection = (ITextSelection) editorPart.getSite().getSelectionProvider().getSelection();
		final int offset = textSelection.getOffset();
		int lineNumber = 0;
		try {
			lineNumber = document.getLineOfOffset(offset);
		} catch (final BadLocationException e) {
			e.printStackTrace();
		}
		return lineNumber;
	}

}
