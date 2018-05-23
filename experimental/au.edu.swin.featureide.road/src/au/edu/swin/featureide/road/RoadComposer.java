package au.edu.swin.featureide.road;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.core.builder.ComposerExtensionClass;

public class RoadComposer extends ComposerExtensionClass {

	@Override
	public void performFullBuild(final IFile config) {
		Display.getDefault().asyncExec(new Runnable() {
			@Override
			public void run() {
				MessageDialog.openInformation(PlatformUI.getWorkbench()
						.getActiveWorkbenchWindow().getShell(),
						"Road - A FeatureIDE extension",
						"Builder startet for configuration " + config.getName()
								+ " in project "
								+ config.getProject().getName());
			}
		});
	}

}
