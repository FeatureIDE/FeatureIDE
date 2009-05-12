package featureide.ui.decorators;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.IDecoration;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ILightweightLabelDecorator;

import featureide.core.CorePlugin;
import featureide.ui.UIPlugin;

public class FeatureProjectDecorator implements ILightweightLabelDecorator {

	private static final ImageDescriptor OVERLAY = UIPlugin.getDefault().getImageDescriptor("icons/FeatureProjectDecorator.png");

	public FeatureProjectDecorator() {
	}
	
	public void dispose() {
	}

	public void decorate(Object element, IDecoration decoration) {
		IProject project = (IProject) element;

		//decorate feature projects
		if (CorePlugin.hasProjectData(project)) {
			UIPlugin.getDefault().logInfo("Decorating feature project");
			decoration.addOverlay(OVERLAY, IDecoration.TOP_RIGHT);
		}
	}

	public void addListener(ILabelProviderListener listener) {
	}

	public void removeListener(ILabelProviderListener listener) {
	}

	public boolean isLabelProperty(Object element, String property) {
		return false;
	}
}
