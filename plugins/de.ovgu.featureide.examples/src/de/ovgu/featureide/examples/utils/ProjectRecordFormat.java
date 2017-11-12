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
package de.ovgu.featureide.examples.utils;

import java.util.Collection;
import java.util.List;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import de.ovgu.featureide.examples.ExamplePlugin;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.AXMLFormat;

/**
 * Reads / Writes the XML structure that holds the paths for all example projects.
 *
 * @author Sebastian Krieter
 */
public class ProjectRecordFormat extends AXMLFormat<ProjectRecordCollection> {

	public static final String ID = ExamplePlugin.PLUGIN_ID + ".format." + ProjectRecordFormat.class.getSimpleName();

	private static final String ATTRIBUTE_PATH = "path";
	private static final String ATTRIBUTE_NAME = "name";
	private static final String PROJECT = "project";
	private static final String PROJECT_RECORDS = "projectRecords";

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public ProjectRecordFormat getInstance() {
		return this;
	}

	@Override
	protected void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException {
		for (final Element e : getElements(doc.getElementsByTagName(PROJECT_RECORDS))) {
			parseProjects(getElements(e.getChildNodes()), object);
		}
	}

	private void parseProjects(List<Element> elements, Collection<ProjectRecord> projectRecords) {
		for (final Element element : elements) {
			if (PROJECT.equals(element.getTagName())) {
				final String name = element.getAttribute(ATTRIBUTE_NAME);
				final String path = element.getAttribute(ATTRIBUTE_PATH);
				final ProjectRecord projectRecord = new ProjectRecord(path, name);
				object.add(projectRecord);
				parseSubProjects(getElements(element.getChildNodes()), projectRecord);
			}
		}
	}

	private void parseSubProjects(List<Element> elements, ProjectRecord parentRecord) {
		for (final Element element : elements) {
			if (PROJECT.equals(element.getTagName())) {
				final String name = element.getAttribute(ATTRIBUTE_NAME);
				final String path = element.getAttribute(ATTRIBUTE_PATH);
				final ProjectRecord projectRecord = new ProjectRecord(path, name);
				parentRecord.addSubProject(projectRecord);
				parseSubProjects(getElements(element.getChildNodes()), projectRecord);
			}
		}
	}

	@Override
	protected void writeDocument(Document doc) {
		final Element root = doc.createElement(PROJECT_RECORDS);
		doc.appendChild(root);
		addProjectRecords(doc, root, object);
	}

	private void addProjectRecords(Document doc, final Element root, Collection<ProjectRecord> projects) {
		for (final ProjectRecord projectRecord : projects) {
			final Element projectElement = doc.createElement(PROJECT);
			root.appendChild(projectElement);
			projectElement.setAttribute(ATTRIBUTE_NAME, projectRecord.getProjectName());
			projectElement.setAttribute(ATTRIBUTE_PATH, projectRecord.getProjectDescriptionRelativePath());
			if (projectRecord.hasSubProjects()) {
				addProjectRecords(doc, projectElement, projectRecord.getSubProjects());
			}
		}
	}

	@Override
	public String getName() {
		return "";
	}

}
