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

import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.net.URL;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import de.ovgu.featureide.examples.ExamplePlugin;
import de.ovgu.featureide.examples.utils.ProjectRecord;

/**
 * 
 * @author Reimar Schroeter
 */
public final class ProjectProvider {

	private static final Collection<ProjectRecord> projects = getProjects();
	private static final Set<String> viewerNames = getViewersNamesForProjects();

	private ProjectProvider() {
	}

	public static Collection<ProjectRecord> getProjects() {
		if (projects != null) {
			return projects;
		}
		InputStream inputStream = null;
		try {
			final URL url = new URL("platform:/plugin/de.ovgu.featureide.examples/projects.s");
			inputStream = url.openConnection().getInputStream();
		} catch (IOException e) {
			ExamplePlugin.getDefault().logError(e);
		}

		return getProjects(inputStream);
	}

	@SuppressWarnings("unchecked")
	private static Collection<ProjectRecord> getProjects(InputStream inputStream) {
		Collection<ProjectRecord> projects = null;
		try (ObjectInputStream stream = new ObjectInputStream(inputStream)) {
			projects = ((Collection<ProjectRecord>) stream.readObject());
		} catch (IOException | ClassNotFoundException | ClassCastException e) {
			ExamplePlugin.getDefault().logError(e);
		}

		if (projects != null) {
			for (ProjectRecord projectRecord : projects) {
				projectRecord.init();
			}
		}
		return projects;
	}

	public static Set<String> getViewersNamesForProjects() {
		if (viewerNames != null) {
			return viewerNames;
		}
		Set<String> viewerNames = new HashSet<>();
		for (ProjectRecord projectRecord : ProjectProvider.getProjects()) {
			final Document doc = projectRecord.getInformationDocument();

			if (doc != null) {
				final NodeList nlInterfaces = doc.getElementsByTagName("contentProvider");
				for (int i = 0; i < nlInterfaces.getLength(); i++) {
					final Node item = nlInterfaces.item(i);
					if (item.getNodeType() == Node.ELEMENT_NODE) {
						viewerNames.add(((Element) item).getAttribute("name"));
					}
				}
			}
		}
		return viewerNames;
	}

	public static void resetProjectItems() {
		for (ProjectRecord projectRecord : getProjects()) {
			projectRecord.resetItems();
		}
	}

}
