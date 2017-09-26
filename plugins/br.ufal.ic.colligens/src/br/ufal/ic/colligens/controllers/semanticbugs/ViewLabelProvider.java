package br.ufal.ic.colligens.controllers.semanticbugs;

import static de.ovgu.featureide.fm.core.localization.StringTable.ERROR;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

import br.ufal.ic.colligens.models.cppchecker.CppCheckerFileLogs;
import br.ufal.ic.colligens.models.cppchecker.CppCheckerLog;

class ViewLabelProvider extends LabelProvider implements ITableLabelProvider {

	@Override
	public String getColumnText(Object obj, int index) {
		switch (index) {
		case 0:
			if (obj instanceof CppCheckerFileLogs) {
				final IFile iFile = ((CppCheckerFileLogs) obj).getFile();
				return iFile.getLocation().toOSString().substring(iFile.getProject().getLocation().toOSString().length(),
						iFile.getLocation().toOSString().length())
					+ " (" + ((CppCheckerFileLogs) obj).getLogs().size() + ERROR + ((((CppCheckerFileLogs) obj).getLogs().size() == 1) ? "" : "s") + ")";
			}
			if (obj instanceof CppCheckerLog) {
				return ((CppCheckerLog) obj).getMsg();
			}
		case 1:
			if (obj instanceof CppCheckerLog) {
				return ((CppCheckerLog) obj).getLine();
			}
		case 2:
			if (obj instanceof CppCheckerLog) {
				return ((CppCheckerLog) obj).getSeverity();
			}
		case 3:
			if (obj instanceof CppCheckerLog) {
				return ((CppCheckerLog) obj).getConfig();
			}
		case 4:
			if (obj instanceof CppCheckerLog) {
				return ((CppCheckerLog) obj).getId();
			}
		default:
			return "";
		}
	}

	@Override
	public Image getColumnImage(Object element, int columnIndex) {
		// TODO Auto-generated method stub
		return null;
	}
}
