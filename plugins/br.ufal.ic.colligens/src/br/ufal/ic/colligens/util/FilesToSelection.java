package br.ufal.ic.colligens.util;

import java.util.Iterator;
import java.util.List;

import org.eclipse.cdt.core.model.ICProject;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.IStructuredSelection;

import br.ufal.ic.colligens.controllers.ProjectExplorerController;

@SuppressWarnings("rawtypes")
public class FilesToSelection implements IStructuredSelection {

	private final List<IResource> list;

	public FilesToSelection(ICProject project, String filePath) {

		final IFolder folder = project.getProject().getFolder(filePath);

		final ProjectExplorerController explorerController = new ProjectExplorerController();

		explorerController.addResource(folder);

		list = explorerController.getList();

	}

	@Override
	public boolean isEmpty() {
		// TODO Auto-generated method stub
		return list.isEmpty();
	}

	@Override
	public Object getFirstElement() {
		// TODO Auto-generated method stub
		return list.get(0);
	}

	@Override
	public Iterator iterator() {
		// TODO Auto-generated method stub
		return list.iterator();
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return list.size();
	}

	@Override
	public Object[] toArray() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List toList() {
		// TODO Auto-generated method stub
		return list;
	}

}
