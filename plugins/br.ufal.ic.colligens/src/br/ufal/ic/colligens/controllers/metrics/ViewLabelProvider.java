package br.ufal.ic.colligens.controllers.metrics;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

import br.ufal.ic.colligens.util.metrics.Metrics;

class ViewLabelProvider extends LabelProvider implements ITableLabelProvider {

	@Override
	public String getColumnText(Object obj, int index) {
		switch (index) {
		case 0:
			if (obj instanceof Metrics) {
				return ((Metrics) obj).getName();
			}
		case 1:
			if (obj instanceof Metrics) {
				return ((Metrics) obj).getValue();
			}
		default:
			return "";
		}
	}

	@Override
	public Image getColumnImage(Object obj, int index) {
		// switch (index) {
		// case 0:
		// return PlatformUI.getWorkbench().getSharedImages()
		// .getImage(ISharedImages.IMG_DEF_VIEW);
		// case 1:
		// return PlatformUI.getWorkbench().getSharedImages()
		// .getImage(ISharedImages.IMG_ELCL_SYNCED);
		// default:
		return null;
		// }

	}
}
