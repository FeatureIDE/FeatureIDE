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
package de.ovgu.featureide.ui.statistics.core;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;

import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * TODO description
 * 
 * @author "Felipe Gustavo de Souza Gomes"
 */
public class SnapshotExporter {

	private List<Parent> parents;
	private Parent godfather;
	private String snapshotsPath;
	private static final String SNAPSHOTS_FOLDER_NAME = "snapshots";

	public SnapshotExporter(Parent parent, IPath projectPath) {
		this.parents = new ArrayList<Parent>();
		this.godfather = parent;

		File projectFolder = projectPath.toFile();
		File snapshotFolder = new File(projectFolder.getAbsolutePath() + File.separatorChar + SNAPSHOTS_FOLDER_NAME);
		if (!snapshotFolder.exists()) {
			snapshotFolder.mkdir();
		}
		this.snapshotsPath = snapshotFolder.getAbsolutePath();
	}

	public void export() {
		createFile();
		setStatistics(godfather);
		for(Parent p : parents){
			System.out.println(p.getDescription()+" >> "+p.getValue());
		}
	}
	
	private void createFile() {
		Date date = new Date();
		long timestamp = date.getTime();

		File resultFile = new File(this.snapshotsPath + File.separatorChar + String.valueOf(timestamp) + ".csv");
		try {
			resultFile.createNewFile();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	private void setStatistics(Object inputElement) {
		Object[] tempParents = null;
		if (!(inputElement instanceof Parent)) {
			tempParents = getChildren(godfather);
		} else {
			tempParents = getChildren(inputElement);
		}

		for (Object o : tempParents) {
			if (o instanceof Parent)
				this.parents.add((Parent) o);
			setStatistics(o);
		}
	}

	private Object[] getChildren(Object parent) {
		if (parent instanceof Parent) {
			return ((Parent) parent).getChildren();
		}
		return null;
	}

}