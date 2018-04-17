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
package de.ovgu.featureide.ui.editors.annotation;

import static de.ovgu.featureide.fm.core.localization.StringTable.CANT_CONNECT_TO_DIFFERENT_DOCUMENT_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CANT_DISCONNECT_FROM_DIFFERENT_DOCUMENT_;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;
import java.util.Vector;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
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
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.builder.IComposerExtensionClass.Mechanism;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;

/**
 * Assigns color annotations to the editor.
 *
 * @author Sebastian Krieter
 */
public final class ColorAnnotationModel implements IAnnotationModel {

	/** Key used to piggyback the model to the editors model. */
	public static final Object KEY = new Object();

	private static boolean highlighting = true;

	/** List of current ColorAnnotations */
	private final List<ColorAnnotation> annotations = new ArrayList<ColorAnnotation>(32);
	private HashMap<Integer, Position> annotatedPositions = new HashMap<Integer, Position>();

	private final HashMap<Integer, FSTDirective> directiveMap = new HashMap<Integer, FSTDirective>();
	private final LinkedList<FSTDirective> validDirectiveList = new LinkedList<FSTDirective>();

	/** List of registered IAnnotationModelListener */
	private final Set<IAnnotationModelListener> annotationModelListeners = new HashSet<IAnnotationModelListener>(2);

	private final IDocument document;
	private final IFeatureProject project;
	private final IComposerExtensionClass composer;
	private final IFile file;

	private int openConnections = 0;
	private int docLines, docLength;

	private final IEventListener colorChangeListener = new IEventListener() {

		@Override
		public void propertyChange(FeatureIDEEvent event) {
			updateAnnotations(true);
		}
	};
	private final IDocumentListener documentListener = new IDocumentListener() {

		@Override
		public void documentChanged(DocumentEvent event) {
			final IDocument newDoc = event.getDocument();
			if (docLines != newDoc.getNumberOfLines()) {
				updateAnnotations(false);
				docLines = newDoc.getNumberOfLines();
				docLength = newDoc.getLength();
			} else {
				changeAnnotations(event.getOffset(), newDoc.getLength());
			}
		}

		@Override
		public void documentAboutToBeChanged(DocumentEvent event) {}
	};

	private ColorAnnotationModel(IDocument document, IFile file, IFeatureProject project, ITextEditor editor) {
		this.document = document;
		this.project = project;
		this.file = file;
		composer = project.getComposer();

		docLines = document.getNumberOfLines();
		docLength = document.getLength();

		FeatureColorManager.addListener(colorChangeListener);

		updateAnnotations(true);

		editor.addPropertyListener(new IPropertyListener() {

			@Override
			public void propertyChanged(Object source, int propId) {
				if ((propId == IEditorPart.PROP_DIRTY) && !((ITextEditor) source).isDirty()) {
					composer.buildFSTModel();
					updateAnnotations(true);
				}
			}
		});
	}

	public IFeatureModel getFeatureModel() {
		return project.getFeatureModel();
	}

	public IFeature getFeature(int line) {
		FSTDirective found = null;
		for (final FSTDirective fst : validDirectiveList) {
			if ((fst.getStartLine() <= line) && (line <= fst.getEndLine())) {
				found = fst;
			}
		}
		if (found == null) {
			return null;
		}
		final String name = found.getFeatureNames().get(0);
		final IFeature feature = project.getFeatureModel().getFeature(name);
		return feature;
	}

	/**
	 * Attaches a coverage annotation model for the given editor if the editor can be annotated. Does nothing if the model is already attached.
	 *
	 * @param editor Editor to attach a annotation model to
	 */
	public static boolean attach(ITextEditor editor) {
		final IDocumentProvider provider = editor.getDocumentProvider();
		final IEditorInput input = editor.getEditorInput();

		if ((provider != null) && (input instanceof FileEditorInput)) {
			final IAnnotationModel model = provider.getAnnotationModel(input);

			if (model instanceof IAnnotationModelExtension) {
				final IAnnotationModelExtension modelex = (IAnnotationModelExtension) model;

				ColorAnnotationModel colormodel = (ColorAnnotationModel) modelex.getAnnotationModel(KEY);

				if (colormodel == null) {
					final IFile file = ((FileEditorInput) input).getFile();
					final IFeatureProject project = CorePlugin.getFeatureProject(file);
					if ((project != null) && (project.getComposer() != null) && project.getComposer().needColor()) {
						final IDocument document = provider.getDocument(input);
						colormodel = new ColorAnnotationModel(document, file, project, editor);
						modelex.addAnnotationModel(KEY, colormodel);
						// colormodel.updateAnnotations(!editor.isDirty());
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
	 * Detaches the coverage annotation model from the given editor. If the editor does not have a model attached, this method does nothing.
	 *
	 * @param editor Editor to detach the annotation model from
	 */
	public static void detach(ITextEditor editor) {
		final IDocumentProvider provider = editor.getDocumentProvider();
		if (provider != null) {
			final IAnnotationModel model = provider.getAnnotationModel(editor.getEditorInput());

			if (model instanceof IAnnotationModelExtension) {
				final IAnnotationModelExtension modelex = (IAnnotationModelExtension) model;

				modelex.removeAnnotationModel(KEY);
			}
		}
	}

	/**
	 * Changes the whether the editor highlights the directives or not.
	 *
	 * Updates the annotations if the value changed.
	 *
	 * @param highlighting true: highlights directives in the editor
	 */
	public static void setHighlighting(boolean highlighting, ITextEditor editor) {
		if (ColorAnnotationModel.highlighting != highlighting) {
			ColorAnnotationModel.highlighting = highlighting;
			attach(editor);
		}
	}

	/**
	 * This method is called, when the document is changed, but the number of lines stays the same.
	 *
	 * It updates the offset and length of annotations, with an offset greater than the CHANGE_OFFSET.
	 *
	 * @param offset the change offset
	 * @param newLength the length of the changed document
	 */
	private void changeAnnotations(int offset, int newLength) {
		final AnnotationModelEvent modelEvent = new AnnotationModelEvent(this);

		for (final ColorAnnotation annotation : annotations) {
			final Position pos = annotation.getPosition();
			if (pos.getOffset() > offset) {
				annotation.updateOffset(newLength - docLength);
				modelEvent.annotationChanged(annotation);
			} else if (pos.includes(offset)) {
				annotation.updateLength(newLength - docLength);
				modelEvent.annotationChanged(annotation);
			}
		}
		docLength = newLength;

		fireModelChanged(modelEvent);
	}

	/**
	 * This method is called, when the document is saved or when the document and the number of lines are changed.
	 *
	 * It removes all annotations and creates new.
	 *
	 * @param createNew true: builds new FSTModel false: only gets new FSTDirectives
	 */
	private void updateAnnotations(boolean createNew) {
		if (!annotations.isEmpty()) {
			clear();
		}
		if (createNew) {
			annotatedPositions = new HashMap<Integer, Position>(docLines);
			if (project.getComposer().getGenerationMechanism() == Mechanism.FEATURE_ORIENTED_PROGRAMMING) {
				try {
					createFOPAnnotations();
				} catch (final BadLocationException e) {
					CorePlugin.getDefault().logError(e);
				}
			} else {
				createDirectiveList();
				createAnnotations();
			}
		} else {
			if (project.getComposer().getGenerationMechanism() == Mechanism.FEATURE_ORIENTED_PROGRAMMING) {
				try {
					createFOPAnnotations();
				} catch (final BadLocationException e) {
					CorePlugin.getDefault().logError(e);
				}
			} else {
				if (!directiveMap.isEmpty()) {
					annotatedPositions.clear();
					updateDirectives();
					createAnnotations();
				}
			}
		}
	}

	/**
	 * Removes all annotations.
	 */
	private void clear() {
		final AnnotationModelEvent event = new AnnotationModelEvent(this);
		for (final ColorAnnotation ca : annotations) {
			event.annotationRemoved(ca, ca.getPosition());
		}
		annotations.clear();

		fireModelChanged(event);
	}

	/**
	 * Builds the FSTModel of the feature project and creates a list of all directives with valid colors
	 *
	 * @return the directive list
	 */
	private void createDirectiveList() {
		directiveMap.clear();
		validDirectiveList.clear();
		FSTModel model = project.getFSTModel();
		if ((model == null) || model.getClasses().isEmpty()) {
			composer.buildFSTModel();
			model = project.getFSTModel();
		}
		if (model == null) {
			return;
		}

		for (final FSTFeature fstFeature : model.getFeatures()) {
			for (final FSTRole role : fstFeature.getRoles()) {
				if (file.equals(role.getFile())) {
					for (final FSTDirective dir : role.getDirectives()) {
						directiveMap.put(dir.getId(), dir);
						validDirectiveList.add(dir);
					}
				}
			}
		}
	}

	/**
	 * Assigns the mapped colors to the FSTDirectives from the changed document.
	 *
	 * @return the directive list
	 */
	private void updateDirectives() {
		final ListIterator<FSTDirective> newDirIt = getNewDirectives().listIterator(0);

		while (newDirIt.hasNext()) {
			final FSTDirective newDir = newDirIt.next();
			final FSTDirective oldDir = directiveMap.get(newDir.getId());

			if ((oldDir != null) && (newDir.getCommand() == oldDir.getCommand()) && newDir.getFeatureNames().equals(oldDir.getFeatureNames())) {

				oldDir.setStartLine(newDir.getStartLine(), newDir.getStartOffset());
				oldDir.setEndLine(newDir.getEndLine(), newDir.getEndLength());
			} else {
				directiveMap.clear();
				return;
			}

			if (newDir.hasChildren()) {
				for (final FSTDirective newDirChild : newDir.getChildrenList()) {
					newDirIt.add(newDirChild);
					newDirIt.previous();
				}
			}
		}
	}

	/**
	 * Retrieves the FSTDirectives from the changed document.
	 */
	private LinkedList<FSTDirective> getNewDirectives() {
		final Vector<String> lines = new Vector<String>();

		for (int i = 0; i < document.getNumberOfLines(); i++) {
			try {
				lines.add(document.get(document.getLineOffset(i), document.getLineLength(i)));
			} catch (final BadLocationException e) {}
		}

		return composer.buildModelDirectivesForFile(lines);
	}

	/**
	 * Creates Annotations for FOP
	 */
	private void createFOPAnnotations() throws BadLocationException {
		final AnnotationModelEvent event = new AnnotationModelEvent(this);
		FSTModel model = project.getFSTModel();

		if (model == null) {
			composer.buildFSTModel();
			model = project.getFSTModel();
		}
		if (model == null) {
			return;
		}

		clear();
		directiveMap.clear();
		validDirectiveList.clear();

		if (file.getParent() instanceof IFolder) {
			if (isInBuildFolder((IFolder) file.getParent())) {
				/* annotations for generated files */
				final FSTClass clazz = model.getClass(model.getAbsoluteClassName(file));
				if (clazz == null) {
					return;
				}
				if (!clazz.hasComposedLines) {
					clazz.hasComposedLines = true;
					composer.postCompile(null, file);
				}
				for (final FSTFeature fstFeature : model.getFeatures()) {
					final FSTRole role = clazz.getRole(fstFeature.getName());
					if (role == null) {
						continue;
					}
					for (final FSTMethod m : role.getAllMethods()) {
						createFOPComposedAnnotations(event, fstFeature, m);
					}
					for (final FSTField f : role.getAllFields()) {
						createFOPComposedAnnotations(event, fstFeature, f);
					}
				}
			} else {
				/* annotations for source files */
				final String featureName = getFeature((IFolder) file.getParent());

				final FSTDirective div = new FSTDirective();
				div.setStartLine(0, 0);
				div.setEndLine(document.getNumberOfLines() - 1, 0);
				div.setFeatureName(featureName);
				directiveMap.put(0, div);
				validDirectiveList.add(div);

				if (featureName != null) {
					final FSTFeature fstFeature = model.getFeature(featureName);
					if (fstFeature != null) {
						// bar at the left of the editor
						final int color = fstFeature.getColor();
						for (int line = 0; line < document.getNumberOfLines(); line++) {
							final Position position = new Position(document.getLineOffset(line), 1);
							final ColorAnnotation cafh = new ColorAnnotation(color, position, ColorAnnotation.TYPE_IMAGE);
							cafh.setText(fstFeature.getName());
							annotations.add(cafh);
							event.annotationAdded(cafh);
						}
					}
				}
			}
		}
	}

	/**
	 * Creates Annotations for FOP Composed File
	 *
	 * @param event
	 * @param fstFeature
	 * @param m
	 * @throws BadLocationException
	 */
	private void createFOPComposedAnnotations(AnnotationModelEvent event, FSTFeature fstFeature, RoleElement<?> m) throws BadLocationException {
		if (m.getComposedLine() <= 0) {
			return;
		}
		final int startline = m.getComposedLine() - 1;
		final int endline = (m.getComposedLine() + m.getMethodLength()) - 1;
		final int lineOffset = document.getLineOffset(startline);
		int length = 0;

		// Add directive to map for coloring issuesq
		final FSTDirective div = new FSTDirective();
		div.setStartLine(startline, 0);
		div.setEndLine(endline, 0);
		div.setFeatureName(m.getRole().getFeature().getName());
		directiveMap.put(directiveMap.size(), div);
		validDirectiveList.add(div);

		for (int line = startline; line <= endline; line++) {
			length += document.getLineLength(line);
			// bar at the left of the editor

			final Position methodposition = new Position(document.getLineOffset(line), document.getLineLength(line));
			final ColorAnnotation cafh = new ColorAnnotation(m.getRole().getFeature().getColor(), methodposition, ColorAnnotation.TYPE_IMAGE);
			cafh.setText(m.getRole().getFeature().getName());
			annotations.add(cafh);
			event.annotationAdded(cafh);
		}

		final Position methodposition = new Position(lineOffset, length);
		// bar at the right of the editor
		final ColorAnnotation cafho = new ColorAnnotation(m.getRole().getFeature().getColor(), methodposition, ColorAnnotation.TYPE_OVERVIEW);
		cafho.setText(m.getRole().getFeature().getName());
		annotations.add(cafho);
		event.annotationAdded(cafho);
		if (highlighting) {
			// background colors
			final ColorAnnotation cafhh = new ColorAnnotation(m.getRole().getFeature().getColor(), methodposition, ColorAnnotation.TYPE_HIGHLIGHT);
			cafhh.setText(fstFeature.getName());
			annotations.add(cafhh);
			event.annotationAdded(cafhh);
		}
	}

	/**
	 * Checks whether the File is in the SourceFolder
	 *
	 * @param folder
	 * @return Feature from the SourceFolder
	 */
	private String getFeature(IFolder folder) {
		final IContainer parent = folder.getParent();
		if (parent.equals(project.getSourceFolder())) {
			return folder.getName();
		}
		if (parent instanceof IFolder) {
			return getFeature((IFolder) parent);
		}
		return null;
	}

	/**
	 * Checks whether the File is in the BuildFolder
	 *
	 * @param folder
	 * @return true if BuildFolder or child of BuildFolder
	 */
	private boolean isInBuildFolder(IFolder folder) {
		if (folder.equals(project.getBuildFolder())) {
			return true;
		}
		final IContainer parent = folder.getParent();
		if (parent instanceof IFolder) {
			return isInBuildFolder((IFolder) parent);
		}
		return false;
	}

	/**
	 * Creates the color annotations from the FSTDirectives.
	 */
	private void createAnnotations() {
		final AnnotationModelEvent event = new AnnotationModelEvent(this);

		for (final FSTDirective directive : validDirectiveList) {
			if (directive == null) {
				continue;
			}
			try {
				final int startline = directive.getStartLine();
				final int endline = getLastChildLine(directive, directive.getEndLine());
				final int color = directive.getColor();
				int overViewStartOffset = document.getLineOffset(startline);
				int overViewLength = 0;
				for (int line = startline; line <= endline; line++) {
					int length = document.getLineLength(line);
					if ((line < endline) || (directive.getEndLength() > 0)) {
						int lineOffset = document.getLineOffset(line);

						if (line == directive.getEndLine()) {
							length = directive.getEndLength();
						}
						if (line == startline) {
							lineOffset += directive.getStartOffset();
							length -= directive.getStartOffset();
						}

						if (hasChildAtLine(directive, line)) {
							length = 1;
						}

						if ((overViewStartOffset != -1) && hasChildAtLineWithColor(directive, line)) {
							final Position overViewPos = new Position(overViewStartOffset, overViewLength);
							createOverViewRuler(event, directive, color, overViewPos);
							overViewStartOffset = -1;
							overViewLength = 0;
						} else if (!hasChildAtLineWithColor(directive, line)) {
							if (overViewStartOffset == -1) {
								overViewStartOffset = document.getLineOffset(line);
							}
							overViewLength += document.getLineLength(line);
						}

						FSTDirective parent = directive.getParent();
						while (parent != null) {
							lineOffset++;
							if (length > 1) {
								length--;
							}
							parent = parent.getParent();
						}
						final Position newPos = new Position(lineOffset, length);

						if (!hasChildAtLine(directive, line)) {
							// bar at the left of the editor
							final ColorAnnotation ca = new ColorAnnotation(color, newPos, ColorAnnotation.TYPE_IMAGE);
							ca.setText(directive.toString());
							annotations.add(ca);
							event.annotationAdded(ca);
						}
						if (!hasChildAtLine(directive, line)) {
							// bar at the right of the editor

						}
						if (highlighting) {
							// background colors
							final ColorAnnotation ca = new ColorAnnotation(color, newPos, ColorAnnotation.TYPE_HIGHLIGHT);
							ca.setText(directive.toDependencyString());
							annotations.add(ca);
							event.annotationAdded(ca);
						}
					}

				}
				if (overViewStartOffset != -1) {
					final Position overViewPos = new Position(overViewStartOffset, overViewLength);
					createOverViewRuler(event, directive, color, overViewPos);
					overViewStartOffset = -1;
					overViewLength = 0;
				}
			} catch (final BadLocationException e) {}
		}

		fireModelChanged(event);
	}

	/**
	 * Creates a new overview ruler annotation.
	 *
	 */
	private void createOverViewRuler(AnnotationModelEvent event, FSTDirective directive, final int color, Position newPos) {
		final ColorAnnotation ca = new ColorAnnotation(color, newPos, ColorAnnotation.TYPE_OVERVIEW);
		ca.setText(directive.toString());
		annotations.add(ca);
		event.annotationAdded(ca);
	}

	/**
	 * Returns whether the given annotation has a child <b>with a color</b> at the given line.
	 *
	 * @param directive The directive
	 * @param line The line
	 * @return <code>true</code> if there is a child at the line
	 */
	private boolean hasChildAtLineWithColor(FSTDirective directive, int line) {
		return hasChildAtLine(directive, line, true);
	}

	/**
	 * Returns whether the given annotation has a child at the given line.
	 *
	 * @param directive The directive
	 * @param line The line
	 * @return <code>true</code> if there is a child at the line
	 */
	private boolean hasChildAtLine(FSTDirective directive, int line) {
		return hasChildAtLine(directive, line, false);
	}

	private boolean hasChildAtLine(FSTDirective directive, int line, boolean hasValidColor) {
		for (final FSTDirective child : directive.getChildren()) {
			final int start = child.getStartLine();
			final int end = child.getEndLine();

			if ((line >= start) && (line <= end) && (!hasValidColor || (child.getColor() != FeatureColor.NO_COLOR.getValue()))) {
				return true;
			}
			if (hasChildAtLine(child, line, hasValidColor)) {
				return true;
			}

		}
		return false;
	}

	private int getLastChildLine(FSTDirective directive, int lastLine) {
		for (final FSTDirective child : directive.getChildren()) {
			int childEnd = child.getEndLine();
			if (child.getEndLength() > 0) {
				childEnd++;
			}
			lastLine = Math.max(childEnd, lastLine);
			lastLine = Math.max(getLastChildLine(child, lastLine), lastLine);
		}
		return lastLine;
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
		if (this.document != document) {
			throw new RuntimeException(CANT_CONNECT_TO_DIFFERENT_DOCUMENT_);
		}
		for (final ColorAnnotation ca : annotations) {
			try {
				document.addPosition(ca.getPosition());
			} catch (final BadLocationException ex) {}
		}
		if (openConnections++ == 0) {
			document.addDocumentListener(documentListener);
		}
	}

	@Override
	public void disconnect(IDocument document) {
		if (this.document != document) {
			throw new RuntimeException(CANT_DISCONNECT_FROM_DIFFERENT_DOCUMENT_);
		}
		for (final ColorAnnotation ca : annotations) {
			document.removePosition(ca.getPosition());
		}
		if (--openConnections == 0) {
			document.removeDocumentListener(documentListener);
		}
		FeatureColorManager.removeListener(colorChangeListener);
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

	@SuppressWarnings({ "rawtypes", "unchecked" })
	@Override
	public Iterator getAnnotationIterator() {
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
