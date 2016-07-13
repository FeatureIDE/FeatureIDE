/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
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
public class DynamicContentProvider extends ProjectProvider {
	private Hashtable<IPath, Set<Object>> pathtoRecord;
	private String contentProviderName;

	public DynamicContentProvider(String contentProviderName) {
		this.contentProviderName = contentProviderName;
	}

	public Object[] getElements(Object inputElement) {
		if (pathtoRecord == null) {
			computeHashtable();
		}
		if (pathtoRecord != null) {
			return pathtoRecord.get(new Path("MYROOT")).toArray();
		} else {
			return new Object[] { EXAMPLES_COULD_NOT_BE_LOADED_ };
		}
	}

	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof IPath) {
			return pathtoRecord.get(parentElement).toArray();
		} else if (parentElement instanceof ProjectRecord.TreeItem) {
			return new Object[0];
		} else {
			return new Object[] { CHILDREN_COULD_NOT_BE_LOADED_ };
		}
	}

	public Object getParent(Object element) {
		if (element instanceof ProjectRecord.TreeItem) {
			for (Entry<IPath, Set<Object>> entries : pathtoRecord.entrySet()) {
				if (entries.getValue().contains(element)) {
					return entries.getKey();
				}
			}
		}
		if (element instanceof IPath) {
			IPath path = (IPath) element;
			IPath returnPath = path.removeLastSegments(1);
			boolean isEmpty = returnPath.isEmpty();
			if (isEmpty) {
				return null;
			}
			return returnPath;
		}
		return null;
	}

	public boolean hasChildren(Object element) {
		if (element instanceof IPath) {
			return pathtoRecord.containsKey((IPath) element) && !pathtoRecord.get((IPath) element).isEmpty();
		} else {
			return false;
		}
	}

	public void dispose() {
	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
	}

	private void computeHashtable() {
		pathtoRecord = new Hashtable<>();
		for (ProjectRecord projectRecord : getProjects()) {
			Document doc = projectRecord.getInformationDocument();
			if (doc == null) {
				continue;
			}
			NodeList nlInterfaces = doc.getElementsByTagName("contentProvider");
			for (int i = 0; i < nlInterfaces.getLength(); i++) {
				if (nlInterfaces.item(i).getNodeType() == Node.ELEMENT_NODE) {
					Element el = ((Element) nlInterfaces.item(i));
					String attribute = el.getAttribute("name");
					if (!attribute.equals(contentProviderName)) {
						continue;
					} else {
						NodeList pathNode = el.getElementsByTagName("path");
						for (int j = 0; j < pathNode.getLength(); j++) {
							if (pathNode.item(j).getNodeType() == Node.ELEMENT_NODE) {
								Element pathEl = ((Element) pathNode.item(j));
								String textContent = pathEl.getTextContent();
								IPath path = new Path(textContent);
								assignProjectToRecPath(projectRecord, path);
							}
						}
					}
				}
			}
		}
	}

	private void assignProjectToRecPath(ProjectRecord projectRecord, IPath path) {
		if (pathtoRecord.containsKey(path)) {
			pathtoRecord.get(path).add(projectRecord.createNewTreeItem(this));
		} else {
			int length = path.segmentCount();
			if (length >= 1) {
				IPath longPath = path;
				while (length >= 1) {
					if (length == 1) {
						if (pathtoRecord.containsKey(new Path("MYROOT"))) {
							pathtoRecord.get(new Path("MYROOT")).add(longPath);
						} else {
							Set<Object> l = new HashSet<Object>();
							l.add(longPath);
							pathtoRecord.put(new Path("MYROOT"), l);
						}
						length = 0;
					} else {
						IPath newPath = path.removeLastSegments(1);
						if (pathtoRecord.containsKey(newPath)) {
							pathtoRecord.get(newPath).add(longPath);
							length = 1;
						} else {
							Set<Object> l = new HashSet<Object>();
							l.add(longPath);
							pathtoRecord.put(newPath, l);
						}
						longPath = newPath;
						length = longPath.segmentCount();
					}
				}
			}
			Set<Object> newProjectSet = new HashSet<Object>();
			newProjectSet.add(projectRecord.createNewTreeItem(this));
			pathtoRecord.put(path, newProjectSet);
		}
	}
}
