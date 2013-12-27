package br.ufal.ic.colligens.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

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
	private ITextSelection iTextSelection;

	public static final String MARKER_TYPE = Colligens.PLUGIN_ID + ".problem";

	public Log(FileProxy fileProxy, int line, String feature, String severity,
			String message) {
		this.fileProxy = fileProxy;

		this.line = line;

		this.feature = feature.trim();

		if (severity == null) {
			this.severity = severity;
		} else {
			this.severity = severity.trim();
		}

		this.message = message.trim();

		try {
			int startline = selection().getStartLine() + 1;
			IMarker marker = this.getFile().createMarker(MARKER_TYPE);
			marker.setAttribute(IMarker.MESSAGE, this.message);
			marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_ERROR);
			marker.setAttribute(IMarker.LINE_NUMBER, startline);
		} catch (CoreException e) {
			// e.printStackTrace();
		} catch (FileNotFoundException e) {
			// e.printStackTrace();
		} catch (IOException e) {
			// e.printStackTrace();
		} catch (BadLocationException e) {
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

	public ITextSelection selection() throws IOException, CoreException,
			BadLocationException {

		if (iTextSelection == null) {
			int offset = 0;
			int correctLine = 0;
			int correctColunm = 0;
			int nextLineNumber = 0;
			boolean notLine = true;

			File parserFile = new File(Colligens.getDefault().getConfigDir()
					.getAbsolutePath()
					+ System.getProperty("file.separator") + "lexOutput.c");

			File file = new File(fileProxy.getFileReal());

			BufferedReader parserFileRead = new BufferedReader(new FileReader(
					parserFile));

			for (int i = 1, k = line - 1; (parserFileRead.readLine() != null)
					&& (i < k); i++)
				;

			final int size = 5;

			List<String> findLine = new ArrayList<String>();

			for (int i = 0; i < size; i++) {
				String temp = parserFileRead.readLine();
				if (temp == null) {
					break;
				}
				findLine.add(temp.trim());
			}

			BufferedReader fileReader = new BufferedReader(new FileReader(file));

			while (!findLine.isEmpty() && notLine) {

				List<String> outline = new ArrayList<String>();

				for (int i = 0; i < findLine.size(); i++) {
					String temp = fileReader.readLine();
					if (temp == null) {
						break;
					}
					outline.add(temp.trim());
				}

				for (correctLine = 0; true; correctLine++) {
					if (compare(findLine, outline)) {
						notLine = false;
						break;
					} else {

						for (int i = 0; i < outline.size() - 1; i++) {
							outline.set(i, outline.get(i + 1));
						}

						String temp = fileReader.readLine();
						if (temp == null) {
							if (outline.size() > 0) {
								outline.remove(outline.size() - 1);
							}
						} else {
							outline.set(outline.size() - 1, temp);
						}
					}

					if (outline.isEmpty()) {
						break;
					}

				}

				if (notLine) {
					nextLineNumber++;
					for (int i = 0; i < findLine.size() - 1; i++) {
						findLine.set(i, findLine.get(i + 1));
					}
					String temp = parserFileRead.readLine();
					if (temp == null) {
						if (findLine.size() > 0) {
							findLine.remove(findLine.size() - 1);
						}
					} else {
						findLine.set(findLine.size() - 1, temp);
					}

					fileReader = new BufferedReader(new FileReader(file));
				}
			}

			correctLine -= nextLineNumber;

			parserFileRead.close();
			fileReader.close();

			IDocument document = this.getDocument();

			offset = document.getLineOffset(correctLine);
			correctColunm = document.getLineLength(correctLine);

			iTextSelection = new LogSelection(correctLine, correctColunm,
					offset);

		}
		return iTextSelection;
	}

	public void setSelection(ITextSelection iTextSelection) {
		this.iTextSelection = iTextSelection;
	}

	private boolean compare(List<String> find, List<String> strings) {
		if (find.size() > strings.size()) {
			return false;
		}
		int i;
		int size = find.size() < strings.size() ? find.size() : strings.size();
		for (i = 0; i < size; i++) {
			if (!strings.get(i).contains(find.get(i))) {
				break;
			}
		}
		if (i == size) {
			return true;
		} else {
			return false;
		}
	}

	private IDocument getDocument() throws CoreException {
		ITextFileBufferManager.DEFAULT.connect(this.getFile().getFullPath(),
				LocationKind.IFILE, null);
		return FileBuffers
				.getTextFileBufferManager()
				.getTextFileBuffer(this.getFile().getFullPath(),
						LocationKind.IFILE).getDocument();
	}
}
