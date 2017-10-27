package de.ovgu.featureide.cloneanalysis.utils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.ui.IMarkerResolution;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;

public class QuickFix implements IMarkerResolution {

	String label;

	QuickFix(String label) {
		this.label = label;
	}

	public String getLabel() {
		return label;
	}

	@Override
	public void run(IMarker marker) {

		String[] problems = null;
		try {
			problems = marker.getAttribute("QuickFixMessage").toString().split(";");
		} catch (CoreException e1) {

			e1.printStackTrace();
		}

		IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();

		for (int i = 0; i < problems.length; i++) {

			IPath path = new Path(problems[i]);

			final IFile file = CloneAnalysisUtils.getFileFromPath(path);

			try {
				IDE.openEditor(page, file, true);

			} catch (PartInitException e) {

				e.printStackTrace();
			}
		}

	}

}