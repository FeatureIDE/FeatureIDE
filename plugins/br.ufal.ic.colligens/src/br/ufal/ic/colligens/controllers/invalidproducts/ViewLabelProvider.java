package br.ufal.ic.colligens.controllers.invalidproducts;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import br.ufal.ic.colligens.util.InvalidProductViewLog;

class ViewLabelProvider extends LabelProvider implements ITableLabelProvider {

	@Override
	public String getColumnText(Object obj, int index) {
		switch (index) {
		case 0:
			if (obj instanceof InvalidProductViewLog) {
				return ((InvalidProductViewLog) obj).getProductName();
			}
		case 1:
			if (obj instanceof InvalidProductViewLog) {
				return ((InvalidProductViewLog) obj).getRelativePath();
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
			return PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_OBJ_FOLDER);
		default:
			return null;
		}

	}
}
