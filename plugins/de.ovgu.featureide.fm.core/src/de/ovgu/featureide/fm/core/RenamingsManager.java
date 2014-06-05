/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.prop4j.Literal;
import org.prop4j.Node;

/**
 * Handles feature renamings.
 * 
 * @author Jens Meinicke
 */
public class RenamingsManager {
	/**
	 * a list containing all renamings since the last save
	 */
	private final List<Renaming> renamings = new LinkedList<Renaming>();
	private final FeatureModel model;
	private IFolder sourceFolder;
	
	/* *****************************************************************
	 * 
	 * Renaming
	 * 
	 *#*****************************************************************/
	
	public RenamingsManager(FeatureModel model) {
		 this.model = model;
	}
	
	public boolean renameFeature(final String oldName, final String newName) {
		final Map<String, Feature> featureTable = model.getFeatureTable();
		if (!featureTable.containsKey(oldName)
				|| featureTable.containsKey(newName)) {
			return false;
		}
		final List<Constraint> constraints = model.getConstraints();
		final List<String> featureOrderList = model.getFeatureOrderList();
		Feature feature = featureTable.remove(oldName);
		feature.setName(newName);
		featureTable.put(newName, feature);
		renamings.add(new Renaming(oldName, newName));
		for (Constraint c : constraints) {
			renameVariables(c.getNode(), oldName, newName);
		}
		
		// update the feature order list
		for (int i = 0;i < featureOrderList.size();i++) {
			if (featureOrderList.get(i).equals(oldName)) {
				featureOrderList.set(i, newName);
				break;
			}
		}
		return true;
	}
	
	public boolean isRenamed() {
		return (!renamings.isEmpty());
	}

	public void performRenamings() {
		final List<Constraint> constraints = model.getConstraints();
		for (Renaming renaming : renamings) {
			for (Constraint c : constraints) {
				renameVariables(c.getNode(), renaming.oldName, renaming.newName);
			}
		}
		renamings.clear();
	};

	public void performRenamings(IFile file) {
		IProject project = ((IResource) file.getAdapter(IFile.class)).getProject();
		String sourceName = model.getFMComposerManager(project).getProjectSourcePath();
		if (!sourceName.isEmpty()) {
			sourceFolder = project.getFolder(sourceName);
			for (Renaming renaming : renamings) {
				if (!performComposerRenamings(renaming.oldName, renaming.newName, project)) {
					moveFolder(renaming.oldName, renaming.newName);
				}
			}
		}
		if (model.getColorschemeTable().getColorFile(project).exists()) {
			model.getColorschemeTable().readColorsFromFile(project);
			model.getColorschemeTable().saveColorsToFile(project);
		}
		renamings.clear();
	}

	private boolean performComposerRenamings(final String oldName,
			final String newName, final IProject project) {
		return model.getFMComposerManager(project).performRenaming(oldName,	newName, project);
	}

	private void moveFolder(String oldName, String newName) {
		try {
			IFolder folder = sourceFolder.getFolder(oldName);
			if (folder.exists()) {
				if (!sourceFolder.getFolder(newName).exists()) {
					IPath newPath = sourceFolder.getFolder(newName)
							.getFullPath();
					folder.move(newPath, true, null);
				} else {
					move(folder, oldName, newName);
				}
			}
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	private void move(IFolder folder, String oldName, String newName)
			throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFile) {
				IFile newfile = sourceFolder.getFolder(newName).getFile(
						res.getName());
				if (!newfile.exists()) {
					res.move(newfile.getRawLocation(), true, null);
				}
			}
			if (res instanceof IFolder) {
				IFolder newfile = sourceFolder.getFolder(newName).getFolder(
						res.getName());
				if (!newfile.exists()) {
					res.move(newfile.getRawLocation(), true, null);
				}
			}
		}
	}

	private void renameVariables(Node node, String oldName, String newName) {
		if (node instanceof Literal) {
			if (oldName.equals(((Literal) node).var))
				((Literal) node).var = newName;
			return;
		}

		for (Node child : node.getChildren())
			renameVariables(child, oldName, newName);
	}
	
	/**
	 * Returns the current name of a feature given its name at the last save.
	 * 
	 * @param name
	 *            name when last saved
	 * @return current name of this feature
	 */
	public String getNewName(String name) {
		for (Renaming renaming : renamings) {
			if (renaming.oldName.equals(name)) {
				return renaming.newName;
			}
		}
		return name;
	}

	/**
	 * Returns the name of a feature at the time of the last save given its
	 * current name.
	 * 
	 * @param name
	 *            current name of a feature
	 * @return name when last saved
	 */
	public String getOldName(String name) {
		for (Renaming renaming : renamings) {
			if (renaming.newName.equals(name)) {
				return renaming.oldName;
			}
		}
		return name;
	}

	public Set<String> getOldFeatureNames() {
		HashSet<String> names = new HashSet<String>(model.getFeatureTable().keySet());
		for (Renaming renaming : renamings) {
			names.remove(renaming.newName);
			names.add(renaming.oldName);
		}
		return names;
	}

	/**
	 * 
	 */
	public void clear() {
		renamings.clear();
	}
}
