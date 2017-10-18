package br.ufal.ic.colligens.util;

import java.io.IOException;

import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.filebuffers.ITextFileBufferManager;
import org.eclipse.core.filebuffers.LocationKind;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.models.FileProxy;

/**
 * @author Thiago Emmanuel
 *
 */
public class Log {

	private final String feature;
	private String severity;
	private final String message;
	private final FileProxy fileProxy;
	private final int line;
	private final int column;
	private ITextSelection iTextSelection;

	public static final String MARKER_TYPE = Colligens.PLUGIN_ID + ".problem";

	public Log(FileProxy fileProxy, int line, int column, String feature, String severity, String message) {
		this.fileProxy = fileProxy;

		this.line = line;
		this.column = column;

		this.feature = feature.trim();

		if (severity == null) {
			this.severity = severity;
		} else {
			this.severity = severity.trim();
		}

		this.message = message.trim();

		try {
			final IMarker marker = getFile().createMarker(MARKER_TYPE);
			marker.setAttribute(IMarker.MESSAGE, this.message);
			marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
			marker.setAttribute(IMarker.LINE_NUMBER, line);
		} catch (final CoreException e) {
			// e.printStackTrace();
		}
	}

	public String getFeature() {
		return feature;
	}

	public String getSeverity() {
		return severity;
	}

	public String getMessage() {
		return message;
	}

	public String getFileName() {
		return fileProxy.getFileName();
	}

	public String getPath() {
		return fileProxy.getPath();
	}

	public String getFullPath() {
		return fileProxy.getFullPath();
	}

	public IFile getFile() {
		return (IFile) fileProxy.getResource();
	}

	public FileProxy getFileProxy() {
		return fileProxy;
	}

	public ITextSelection selection() throws IOException, CoreException, BadLocationException {

		if (iTextSelection == null) {

			final IDocument document = getDocument();

			final int offset = document.getLineOffset(line - 1);

			final int length = document.getLineOffset(line) - document.getLineOffset(line - 1);

			iTextSelection = new LogSelection(line, length - column, offset + column);

		}
		return iTextSelection;
	}

	public void setSelection(ITextSelection iTextSelection) {
		this.iTextSelection = iTextSelection;
	}

	private IDocument getDocument() throws CoreException {
		ITextFileBufferManager.DEFAULT.connect(getFile().getFullPath(), LocationKind.IFILE, null);
		return FileBuffers.getTextFileBufferManager().getTextFileBuffer(getFile().getFullPath(), LocationKind.IFILE).getDocument();
	}
}
