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
package de.ovgu.featureide.ui.editors.annotation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.DocumentEvent;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentListener;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.AnnotationModelEvent;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.IAnnotationModelExtension;
import org.eclipse.jface.text.source.IAnnotationModelListener;
import org.eclipse.jface.text.source.IAnnotationModelListenerExtension;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.ColorList;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Assigns color annotations to the editor.
 * 
 * @author Sebastian Krieter
 */
public final class ColorAnnotationModel implements IAnnotationModel {

	/** Key used to piggyback the model to the editors model. */
	private static final Object KEY = new Object();
	
	private static boolean highlighting = true;

	/** List of current ColorAnnotations */
	private List<ColorAnnotation> annotations = new ArrayList<ColorAnnotation>(32);
	private HashMap<Integer, Position> annotatedPositions = new HashMap<Integer, Position>();

	private HashMap<Integer, FSTDirective> directiveMap = new HashMap<Integer, FSTDirective>();
	private LinkedList<FSTDirective> validDirectiveList = new LinkedList<FSTDirective>();

	/** List of registered IAnnotationModelListener */
	private Set<IAnnotationModelListener> annotationModelListeners = new HashSet<IAnnotationModelListener>(2);

	private final IDocument document;
	private final IFeatureProject project;
	private final IComposerExtension composer;
	private final IFile file;
	
	private int openConnections = 0;
	private int docLines, docLength;

	private IDocumentListener documentListener = new IDocumentListener() {
		@Override
		public void documentChanged(DocumentEvent event) {
			IDocument newDoc = event.getDocument();
			if (docLines != newDoc.getNumberOfLines()) {
				updateAnnotations(false);
				docLines = newDoc.getNumberOfLines();
				docLength = newDoc.getLength();
			} else {
				changeAnnotations(event.getOffset(), newDoc.getLength());
			}
		}

		@Override
		public void documentAboutToBeChanged(DocumentEvent event) {
		}
	};
	
	private ColorAnnotationModel(IDocument document, IFile file, IFeatureProject project, ITextEditor editor) {
		this.document = document;
		this.project = project;
		this.file = file;
		composer = project.getComposer();
		composer.initialize(project);
		
		docLines = document.getNumberOfLines();
		docLength = document.getLength();
		
		updateAnnotations(true);
		
		editor.addPropertyListener(new IPropertyListener() {
			@Override
			public void propertyChanged(Object source, int propId) {
				if (propId == IEditorPart.PROP_DIRTY && !((ITextEditor) source).isDirty()) {
					updateAnnotations(true);
				}
			}
		});
	}

	/**
	 * Attaches a coverage annotation model for the given editor if the editor
	 * can be annotated. Does nothing if the model is already attached.
	 * 
	 * @param editor
	 *            Editor to attach a annotation model to
	 */	
	public static boolean attach(ITextEditor editor) {
		IDocumentProvider provider = editor.getDocumentProvider();
		IEditorInput input = editor.getEditorInput();
		
		if (provider != null && input instanceof FileEditorInput) {
			IAnnotationModel model = provider.getAnnotationModel(input);

			if (model instanceof IAnnotationModelExtension) {
				IAnnotationModelExtension modelex = (IAnnotationModelExtension) model;
				
				ColorAnnotationModel colormodel = (ColorAnnotationModel) modelex.getAnnotationModel(KEY);
				
				if (colormodel == null) {
					IFile file = ((FileEditorInput) input).getFile();
					IFeatureProject project = CorePlugin.getFeatureProject(file);
					if (project != null && project.getComposer()!=null&&project.getComposer().needColor()) {
						IDocument document = provider.getDocument(input);
						colormodel = new ColorAnnotationModel(document, file, project, editor);
						modelex.addAnnotationModel(KEY, colormodel);
						
						return true;
					}
				} else {
					colormodel.updateAnnotations(!editor.isDirty());
				}
			}
		}
		return false;
	}

	/**
	 * Detaches the coverage annotation model from the given editor. If the
	 * editor does not have a model attached, this method does nothing.
	 * 
	 * @param editor
	 *            Editor to detach the annotation model from
	 */
	public static void detach(ITextEditor editor) {
		IDocumentProvider provider = editor.getDocumentProvider();
		if (provider != null) {
			IAnnotationModel model = provider.getAnnotationModel(editor.getEditorInput());

			if (model instanceof IAnnotationModelExtension) {
				IAnnotationModelExtension modelex = (IAnnotationModelExtension) model;

				modelex.removeAnnotationModel(KEY);
			}
		}
	}
	
	/**
	 * Changes the whether the editor highlights the directives or not.
	 * 
	 * Updates the annotations if the value changed.
	 * 
	 * @param highlighting 
	 *			true: highlights directives in the editor
	 */
	public static void setHighlighting(boolean highlighting, ITextEditor editor) {
		if (ColorAnnotationModel.highlighting != highlighting) {
			ColorAnnotationModel.highlighting = highlighting;
			attach(editor);
		}
	}
	
	/**
	 * This method is called, when the document is changed,
	 * but the number of lines stays the same.
	 * 
	 * It updates the offset and length of annotations, 
	 * with an offset greater than the "change offset".
	 *  
	 *  @param offset the change offset
	 *  @param newLength the length of the changed document
	 */
	private void changeAnnotations(int offset, int newLength) {
		AnnotationModelEvent modelEvent = new AnnotationModelEvent(this);
		
		for (ColorAnnotation annotation : annotations) {
			Position pos = annotation.getPosition();
			if (pos.getOffset() > offset) {
				annotation.updateOffset(newLength - docLength);
				modelEvent.annotationChanged(annotation);
			}
			else if (pos.includes(offset)) {
				annotation.updateLength(newLength - docLength);
				modelEvent.annotationChanged(annotation);
			}
		}
		docLength = newLength;
		
		fireModelChanged(modelEvent);
	}
	
	/**
	 * This method is called, when the document is saved or
	 * when the document and the number of lines are changed.
	 * 
	 * It removes all annotations and creates new.
	 *  
	 *  @param createNew 
	 *  	true: builds new FSTModel
	 *  	false: only gets new FSTDirectives				 
	 */
	private void updateAnnotations(boolean createNew) {
		if (!annotations.isEmpty()) {
			clear();
		}
		if (createNew) {
			annotatedPositions = new HashMap<Integer, Position>(docLines);
			createDirectiveList();
			createAnnotations();
		} else if (!directiveMap.isEmpty()) {
			annotatedPositions.clear();
			updateDirectives();
			createAnnotations();
		}
	}
	
	/**
	 * Removes all annotations.		 
	 */
	private void clear() {
		AnnotationModelEvent event = new AnnotationModelEvent(this);
		for (final ColorAnnotation ca : annotations) {
			event.annotationRemoved(ca, ca.getPosition());
		}
		annotations.clear();
		
		fireModelChanged(event);
	}
	
	/**
	 *  Builds the FSTModel of the feature project and
	 *  creates a list of all directives with valid colors
	 *  
	 *  @return the directive list
	 */
	private void createDirectiveList() {
		directiveMap.clear();
		validDirectiveList.clear();
		FSTModel model = project.getFSTModel();
		if (model == null) {
			composer.buildFSTModel();
			model = project.getFSTModel();
		}
		if (model == null) {
			return;
		}
		
		int index = 0;
		for (FSTFeature fstFeature : model.getFeatures()) {
			for (FSTRole role : fstFeature.getRoles()) {
				if (file.equals(role.getFile())) {
					for (FSTDirective dir : role.getDirectives()) {
						directiveMap.put(dir.getId(), dir);
						index++;
					}
				}
			}
		}
		
		for (int i = 0; i < index; i++) {
			FSTDirective dir = directiveMap.get(i);
			if (dir != null && ColorList.isValidColor(dir.getColor())) {
				validDirectiveList.add(dir);
			}
		}
	}
	
	/**
	 *  Assigns the mapped colors to the FSTDirectives 
	 *  from the changed document.
	 *  
	 *  @return the directive list
	 */
	private void updateDirectives() {	
		ListIterator<FSTDirective> newDirIt = getNewDirectives().listIterator(0);
		
		while(newDirIt.hasNext()) {
			FSTDirective newDir = newDirIt.next();
			FSTDirective oldDir = directiveMap.get(newDir.getId());
				
			if (oldDir != null &&
					newDir.getCommand() == oldDir.getCommand() &&
					newDir.getFeatureNames().equals(oldDir.getFeatureNames())) {
			
				oldDir.setStartLine(newDir.getStartLine(), newDir.getStartOffset());
				oldDir.setEndLine(newDir.getEndLine(), newDir.getEndLength());
			} else {
				directiveMap.clear();
				return;
			}
			
			if (newDir.hasChildren()) {
				for (FSTDirective newDirChild : newDir.getChildrenList()) {
					newDirIt.add(newDirChild);
					newDirIt.previous();
				}
			}
		}
	}
	
	/**
	 *  Retrieves the FSTDirectives from the changed document.
	 */
	private LinkedList<FSTDirective> getNewDirectives() {
		Vector<String> lines = new Vector<String>();
		
		for (int i = 0; i < document.getNumberOfLines(); i++) {
			try {
				lines.add(document.get(document.getLineOffset(i), document.getLineLength(i)));
			} catch (BadLocationException e) {
				UIPlugin.getDefault().logError(e);
			}
		}
		
		return composer.buildModelDirectivesForFile(lines);
	}
	
	/**
	 *  Creates the color annotations from the FSTDirectives.
	 */
	private void createAnnotations() {
		AnnotationModelEvent event = new AnnotationModelEvent(this);
		
		Iterator<FSTDirective> it = validDirectiveList.descendingIterator();
		while (it.hasNext()) {
			FSTDirective dir = it.next();
			try {
				int startline = dir.getStartLine();
				int endline = dir.getEndLine();
				for (int i = startline; i <= endline; i++) {
					if (i < endline || dir.getEndLength() > 0) {
						int lineLength = document.getLineLength(i);
						int lineOffset = document.getLineOffset(i);
						
						if (i == endline) {
							lineLength = dir.getEndLength();
						}
						if (i == startline) {
							lineOffset += dir.getStartOffset();
							lineLength -= dir.getStartOffset();
						}
						
						Position newPos = new Position(lineOffset, lineLength);
						
						if (!annotatedPositions.containsKey(i)) {
							if(!ColorList.isValidColor(dir.getColor()))break;
							ColorAnnotation ca = new ColorAnnotation(dir.getColor(), 
									new Position(lineOffset, lineLength), ColorAnnotation.TYPE_IMAGE);
							annotations.add(ca);
							event.annotationAdded(ca);
							
							if (highlighting) {
								ca = new ColorAnnotation(dir.getColor(), newPos, 
										i == startline ? ColorAnnotation.TYPE_HIGHLIGHT_OVERVIEW : ColorAnnotation.TYPE_HIGHLIGHT);
								annotations.add(ca);
								event.annotationAdded(ca);
							} else if (i == startline) {
								ca = new ColorAnnotation(dir.getColor(), newPos, ColorAnnotation.TYPE_OVERVIEW);
								annotations.add(ca);
								event.annotationAdded(ca);
							}
							
							annotatedPositions.put(i, newPos);
						} else if (highlighting) {
							Position oldPos = annotatedPositions.get(i);
							int oldOffset = oldPos.getOffset();
							int oldLength = oldPos.getLength();
							int wholeOffset = oldOffset;
							int wholeLength = oldLength;
							
							if (oldOffset > lineOffset) {
								ColorAnnotation ca = new ColorAnnotation(dir.getColor(), 
										new Position(lineOffset, oldOffset-lineOffset), ColorAnnotation.TYPE_HIGHLIGHT);
								annotations.add(ca);
								event.annotationAdded(ca);
								wholeOffset = lineOffset; 
								wholeLength += oldOffset-lineOffset;
							}
							int newOffset = oldOffset + oldLength;
							int newLength = lineLength - (newOffset - lineOffset);
							if (newLength > 0) {
								newPos.setOffset(newOffset);
								newPos.setLength(newLength);
								
								ColorAnnotation ca = new ColorAnnotation(dir.getColor(), newPos, ColorAnnotation.TYPE_HIGHLIGHT);
								annotations.add(ca);
								event.annotationAdded(ca);
								
								wholeLength += newLength;
							}
							annotatedPositions.put(i, new Position(wholeOffset, wholeLength));
						}
					}
				}
			} catch (BadLocationException e) {
				UIPlugin.getDefault().logError(e);
			}
		}
		
		fireModelChanged(event);
	}
	
	private void fireModelChanged(AnnotationModelEvent event) {
		event.markSealed();
		if (!event.isEmpty()) {
			for (final IAnnotationModelListener l : annotationModelListeners) {
				if (l instanceof IAnnotationModelListenerExtension) {
					((IAnnotationModelListenerExtension) l).modelChanged(event);
				} else {
					l.modelChanged(this);
				}
			}
		}
	}
	
	@Override
	public void addAnnotationModelListener(IAnnotationModelListener listener) {
		if (!annotationModelListeners.contains(listener)) {
			annotationModelListeners.add(listener);
			fireModelChanged(new AnnotationModelEvent(this, true));
		}
	}

	@Override
	public void removeAnnotationModelListener(IAnnotationModelListener listener) {
		annotationModelListeners.remove(listener);
	}

	@Override
	public void connect(IDocument document) {
		if (this.document != document)
			throw new RuntimeException("Can't connect to different document.");
		for (final ColorAnnotation ca : annotations) {
			try {
				document.addPosition(ca.getPosition());
			} catch (BadLocationException ex) {
			}
		}
		if (openConnections++ == 0) {
			document.addDocumentListener(documentListener);
		}
	}

	@Override
	public void disconnect(IDocument document) {
		if (this.document != document)
			throw new RuntimeException("Can't disconnect from different document.");
		for (final ColorAnnotation ca : annotations) {
			document.removePosition(ca.getPosition());
		}
		if (--openConnections == 0) {
			document.removeDocumentListener(documentListener);
		}
	}

	/**
	 * External modification is not supported.
	 */
	@Override
	public void addAnnotation(Annotation annotation, Position position) {
		throw new UnsupportedOperationException();
	}

	/**
	 * External modification is not supported.
	 */
	@Override
	public void removeAnnotation(Annotation annotation) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterator<?> getAnnotationIterator() {
		return annotations.iterator();
	}

	@Override
	public Position getPosition(Annotation annotation) {
		if (annotation instanceof ColorAnnotation) {
			return ((ColorAnnotation) annotation).getPosition();
		} else {
			return null;
		}
	}
}
