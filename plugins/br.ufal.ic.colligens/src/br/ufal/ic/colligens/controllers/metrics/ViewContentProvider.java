package br.ufal.ic.colligens.controllers.metrics;

import java.util.List;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;

class ViewContentProvider implements IStructuredContentProvider {

	@Override
	public void inputChanged(Viewer v, Object oldInput, Object newInput) {}

	@Override
	public void dispose() {}

	@Override
	public Object[] getElements(Object parent) {
		if (parent instanceof List) {
			return ((List<?>) parent).toArray();
		}
		return new Object[0];
	}
}
