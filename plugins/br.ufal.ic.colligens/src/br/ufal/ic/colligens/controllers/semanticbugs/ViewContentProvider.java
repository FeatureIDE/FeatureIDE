package br.ufal.ic.colligens.controllers.semanticbugs;

import java.util.Collection;
import java.util.List;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

import br.ufal.ic.colligens.models.cppchecker.CppCheckerFileLogs;
import br.ufal.ic.colligens.models.cppchecker.CppCheckerLog;

/*
 * The content provider class is responsible for providing objects to the
 * view. It can wrap existing objects in adapters or simply return objects
 * as-is. These objects may be sensitive to the current input of the view,
 * or ignore it and always show the same content (like Task List, for
 * example).
 */

class ViewContentProvider implements ITreeContentProvider {

	@Override
	public void inputChanged(Viewer v, Object oldInput, Object newInput) {}

	@Override
	public void dispose() {}

	@Override
	public Object[] getElements(Object files) {
		return getChildren(files);
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof List) {
			return ((List<?>) parentElement).toArray();
		}
		if (parentElement instanceof CppCheckerFileLogs) {
			final Collection<CppCheckerLog> logs = ((CppCheckerFileLogs) parentElement).getLogs();

			return logs.toArray();
		}
		return new Object[0];
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof CppCheckerLog) {
			return ((CppCheckerLog) element).getFileLogs();
		}
		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof List) {
			return ((List<?>) element).size() > 0;
		}
		if (element instanceof CppCheckerFileLogs) {
			return (!((CppCheckerFileLogs) element).getLogs().isEmpty());
		}
		return false;
	}
}
