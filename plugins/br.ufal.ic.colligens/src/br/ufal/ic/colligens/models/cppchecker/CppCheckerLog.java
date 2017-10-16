package br.ufal.ic.colligens.models.cppchecker;

import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.filebuffers.ITextFileBufferManager;
import org.eclipse.core.filebuffers.LocationKind;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;

import br.ufal.ic.colligens.activator.Colligens;

public class CppCheckerLog implements ITextSelection {

	private final CppCheckerFileLogs file;
	private final String line;
	private final String id;
	private final String severity;
	private final String msg;
	private final String config;

	public static final String MARKER_TYPE = Colligens.PLUGIN_ID + ".problem";
	private final IDocument document = null;

	public CppCheckerLog(CppCheckerFileLogs file, String line, String id, String severity, String msg, String config) {

		this.file = file;
		this.line = line;
		this.id = id;
		this.severity = severity;
		this.msg = msg;
		this.config = config;

		try {
			final int startline = getStartLine() + 1;
			final IMarker marker = this.file.getFile().createMarker(MARKER_TYPE);
			marker.setAttribute(IMarker.MESSAGE, msg);
			marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
			marker.setAttribute(IMarker.LINE_NUMBER, startline);
		} catch (final CoreException e) {
			e.printStackTrace();
		}

	}

	public CppCheckerFileLogs getFileLogs() {
		return file;
	}

	public String getLine() {
		return line;
	}

	public String getId() {
		return id;
	}

	public String getSeverity() {
		return severity;
	}

	public String getMsg() {
		return msg;
	}

	public String getConfig() {
		return config;
	}

	@Override
	public boolean isEmpty() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int getOffset() {
		IDocument document;
		try {
			document = getDocument();
			return document.getLineOffset(getStartLine());
		} catch (final CoreException e) {
			return 0;
		} catch (final BadLocationException e) {
			return 0;
		}
	}

	@Override
	public int getLength() {
		IDocument document;
		try {
			document = getDocument();
			return document.getLineLength(getStartLine());
		} catch (final CoreException e) {
			return 0;
		} catch (final BadLocationException e) {
			return 0;
		}
	}

	@Override
	public int getStartLine() {
		// TODO Auto-generated method stub
		return Integer.parseInt(line) - 1;
	}

	@Override
	public int getEndLine() {
		// TODO Auto-generated method stub
		return Integer.parseInt(line);
	}

	@Override
	public String getText() {
		// TODO Auto-generated method stub
		return null;
	}

	private IDocument getDocument() throws CoreException {
		if (document != null) {
			return document;
		}
		ITextFileBufferManager.DEFAULT.connect(getFileLogs().getFile().getFullPath(), LocationKind.IFILE, null);
		return FileBuffers.getTextFileBufferManager().getTextFileBuffer(getFileLogs().getFile().getFullPath(), LocationKind.IFILE).getDocument();
	}

}
