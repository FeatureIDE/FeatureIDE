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
package de.ovgu.featureide.fm.ui.views.outline.custom;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

/**
 * Provides all data needed for the FeatureIDE Outline
 * 
 * @author Christopher Sontag
 */
public abstract class OutlineProvider {
	
	private ITreeContentProvider treeProvider = null;
	private OutlineLabelProvider labelProvider = null;
	private List<Action> actions = new ArrayList<>();
	
	public OutlineProvider() {
	}

	public OutlineProvider(ITreeContentProvider treeProvider, OutlineLabelProvider labelProvider) {
		this.treeProvider = treeProvider;
		this.labelProvider = labelProvider;
	}
	
	public void addAction(Action action) {
		actions.add(action);
	}

	public ITreeContentProvider getTreeProvider() {
		return treeProvider;
	}

	public void setTreeProvider(ITreeContentProvider treeProvider) {
		this.treeProvider = treeProvider;
	}

	public OutlineLabelProvider getLabelProvider() {
		return labelProvider;
	}

	public void setLabelProvider(OutlineLabelProvider labelProvider) {
		this.labelProvider = labelProvider;
	}

	public abstract boolean checkSupported(String extension);

	public List<Action> getActions() {
		return actions;
	}

	public void setActions(List<Action> actions) {
		this.actions = actions;
	}
	
	public abstract void handleUpdate(Viewer viewer, IFile iFile);
}
