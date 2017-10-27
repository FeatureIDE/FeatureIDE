package de.ovgu.featureide.cloneanalysis.markers;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaModelMarker;

public class CloneAnalysisMarkers {

	public static final String MARKER_ID = "de.ovgu.featureide.cloneanalysis.cloneMarker";

	public static void addMarker(IFile file, String message, int lineNumber, int severity) {
		try {
			IMarker marker = file.createMarker(MARKER_ID);
			marker.setAttribute(IMarker.MESSAGE, message);
			marker.setAttribute(IMarker.SEVERITY, severity);
			if (lineNumber == -1) {
				lineNumber = 1;
			}
			marker.setAttribute(IMarker.LINE_NUMBER, lineNumber);
		} catch (CoreException e) {
		}
	}

	public static final String TEXT_MARKER = "org.eclipse.core.resources.textmarker";

	public static void addTextMarker(IFile file, String message, int lineNumber, int severity) {
		try {
			IMarker marker = file.createMarker(TEXT_MARKER);
			marker.setAttribute(IMarker.MESSAGE, message);
			marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
			if (lineNumber == -1) {
				lineNumber = 1;
			}
			marker.setAttribute(IMarker.LINE_NUMBER, lineNumber);
		} catch (CoreException e) {
		}
		// Map attribs = new HashMap();
		// for (int i = 0; i < 8; i++) {
		// attribs.put(IMarker.SEVERITY, new Integer(IMarker.SEVERITY_WARNING));
		// attribs.put(IMarker.MESSAGE, message);
		// org.eclipse.ui.texteditors.MarkerUtilities.createMarker(file,
		// attribs, IMarker.PROBLEM);
		// }
	}

	public static void addProblemMarker(IFile file, String message, String formattedMessage, int lineIndex,
			int startChar, int endChar) {

		try {
			IMarker marker = file.createMarker(IMarker.PROBLEM);
			marker.setAttribute(IMarker.MESSAGE, formattedMessage);
			marker.setAttribute(IMarker.SEVERITY, IMarker.SEVERITY_WARNING);
			marker.setAttribute(IMarker.LINE_NUMBER, lineIndex);
			marker.setAttribute(IMarker.CHAR_START, startChar);
			marker.setAttribute(IMarker.CHAR_END, endChar);
			marker.setAttribute(IJavaModelMarker.ID, 1244);
			marker.setAttribute("QuickFixMessage", message);
		} catch (CoreException e) {
			System.out.println("Marker creation failed");
			e.printStackTrace();
		}
	}

}
