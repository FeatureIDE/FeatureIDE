package br.ufal.ic.colligens.controllers.invalidconfigurations;

import static de.ovgu.featureide.fm.core.localization.StringTable.ERROR;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import br.ufal.ic.colligens.models.FileProxy;
import br.ufal.ic.colligens.util.Log;

class ViewLabelProvider extends LabelProvider implements ITableLabelProvider {

	@Override
	public String getColumnText(Object obj, int index) {
		switch (index) {
		case 0:
			if (obj instanceof FileProxy) {
				return ((FileProxy) obj).getFileName() + " (" + ((FileProxy) obj).getLogs().size() + ERROR
					+ ((((FileProxy) obj).getLogs().size() == 1) ? "" : "s") + ")";
			}
			if (obj instanceof Log) {
				return ((Log) obj).getMessage();
			}
		case 1:
			if (obj instanceof Log) {
				return ((Log) obj).getFileName();
			}
		case 2:
			if (obj instanceof Log) {
				return ((Log) obj).getPath();
			}
		case 3:
			if (obj instanceof Log) {
				return ((Log) obj).getFeature();
			}
		case 4:
			if (obj instanceof Log) {
				return ((Log) obj).getSeverity();
			}
		default:
			return "";
		}
	}

	@Override
	public Image getColumnImage(Object obj, int index) {
		switch (index) {
		case 0:
			return PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_OBJS_ERROR_TSK);
		case 1:
			if (obj instanceof Log) {
				return PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_OBJ_FILE);
			}
		case 2:
			if (obj instanceof Log) {
				return PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_OBJ_FOLDER);
			}
		default:
			return null;
		}

	}
}
