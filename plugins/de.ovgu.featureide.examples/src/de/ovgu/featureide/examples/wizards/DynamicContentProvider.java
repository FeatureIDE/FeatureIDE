/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.examples.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.CHILDREN_COULD_NOT_BE_LOADED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXAMPLES_COULD_NOT_BE_LOADED_;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import de.ovgu.featureide.examples.utils.ProjectRecord;

/**
 *
 * @author Reimar Schroeter
 */
public class DynamicContentProvider implements ITreeContentProvider {

	private HashMap<IPath, Set<Object>> pathToRecord;
	private final String contentProviderName;

	public DynamicContentProvider(String contentProviderName) {
		this.contentProviderName = contentProviderName;
	}

	@Override
	public Object[] getElements(Object inputElement) {
		if (pathToRecord == null) {
			computeHashtable();
		}
		if (pathToRecord != null) {
			return pathToRecord.get(new Path("MYROOT")).toArray();
		} else {
			return new Object[] { EXAMPLES_COULD_NOT_BE_LOADED_ };
		}
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IPath) {
			return pathToRecord.get(parentElement).toArray();
		} else if (parentElement instanceof ProjectRecord.TreeItem) {
			return new Object[0];
		} else {
			return new Object[] { CHILDREN_COULD_NOT_BE_LOADED_ };
		}
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof ProjectRecord.TreeItem) {
			for (final Entry<IPath, Set<Object>> entries : pathToRecord.entrySet()) {
				if (entries.getValue().contains(element)) {
					return entries.getKey();
				}
			}
		} else if (element instanceof IPath) {
			final IPath returnPath = ((IPath) element).removeLastSegments(1);
			if (returnPath.isEmpty()) {
				return null;
			}
			return returnPath;
		}
		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof IPath) {
			return pathToRecord.containsKey(element) && !pathToRecord.get(element).isEmpty();
		} else {
			return false;
		}
	}

	@Override
	public void dispose() {}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

	// TODO read XML only once
	private void computeHashtable() {
		pathToRecord = new HashMap<>();
		for (final ProjectRecord projectRecord : ProjectProvider.getProjects()) {
			final Document doc = projectRecord.getInformationDocument();
			if (doc != null) {
				final NodeList nlInterfaces = doc.getElementsByTagName("contentProvider");
				for (int i = 0; i < nlInterfaces.getLength(); i++) {
					final Node item1 = nlInterfaces.item(i);
					if (item1.getNodeType() == Node.ELEMENT_NODE) {
						final Element el = ((Element) item1);
						if (el.getAttribute("name").equals(contentProviderName)) {
							final NodeList pathNode = el.getElementsByTagName("path");
							for (int j = 0; j < pathNode.getLength(); j++) {
								final Node item2 = pathNode.item(j);
								if (item2.getNodeType() == Node.ELEMENT_NODE) {
									assignProjectToRecPath(projectRecord, new Path(((Element) item2).getTextContent()));
								}
							}
						}
					}
				}
			}
		}
	}

	private void assignProjectToRecPath(ProjectRecord projectRecord, IPath path) {
		Set<Object> record = pathToRecord.get(path);
		if (record == null) {
			record = new HashSet<>();
			pathToRecord.put(path, record);

			int length = path.segmentCount();
			while (length > 0) {
				final IPath parent;
				if (length == 1) {
					parent = new Path("MYROOT");
					length = 0;
				} else {
					parent = path.removeLastSegments(1);
					length = parent.segmentCount();
				}
				final Set<Object> parentRecord = pathToRecord.get(parent);
				if (parentRecord != null) {
					parentRecord.add(path);
					break;
				} else {
					final Set<Object> children = new HashSet<>();
					children.add(path);
					pathToRecord.put(parent, children);
				}
				path = parent;
			}
		}
		record.add(projectRecord.createNewTreeItem(this));
	}

}
