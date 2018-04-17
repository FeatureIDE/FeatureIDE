package br.ufal.ic.colligens.controllers.invalidconfigurations;

import java.util.List;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

import br.ufal.ic.colligens.models.FileProxy;
import br.ufal.ic.colligens.util.Log;

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
		if (parentElement instanceof FileProxy) {
			final List<Log> logs = ((FileProxy) parentElement).getLogs();
			return logs.toArray();
		}
		return new Object[0];
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof Log) {
			return ((Log) element).getFileProxy();
		}
		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof List) {
			return ((List<?>) element).size() > 0;
		}
		if (element instanceof FileProxy) {
			return (!((FileProxy) element).getLogs().isEmpty());
		}
		return false;
	}
}
