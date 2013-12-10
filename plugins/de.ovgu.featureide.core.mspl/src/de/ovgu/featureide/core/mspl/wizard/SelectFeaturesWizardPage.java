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
package de.ovgu.featureide.core.mspl.wizard;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * A Wizard Page to select the features from the other project to create the
 * interface.
 * 
 * @author Christoph Giesel
 */
public class SelectFeaturesWizardPage extends WizardPage implements
		SelectionListener {

	private Composite container;
	private Tree featuresTree;
	private SelectProjectWizardPage selectProject;

	public SelectFeaturesWizardPage(SelectProjectWizardPage pageBefore) {
		super("Select Features");
		selectProject = pageBefore;
		setTitle("Select Features");
		setDescription("Here you select the features for the new interface.");
	}

	@Override
	public void createControl(Composite parent) {
		container = new Composite(parent, SWT.NONE);

		FillLayout layout = new FillLayout();
		container.setLayout(layout);

		featuresTree = new Tree(container, SWT.MULTI | SWT.CHECK);
		featuresTree.addSelectionListener(this);

		// Required to avoid an error in the system
		setControl(container);
		setPageComplete(false);
	}

	@Override
	public void setVisible(boolean visible) {
		super.setVisible(visible);

		IProject project = selectProject.getSelectedProject();

		if (project == null) {
			System.err.println("project is null");
			return; // TODO: error handling
		}

		IFeatureProject featureProject = CorePlugin.getFeatureProject(project);

		if (featureProject == null) {
			System.err.println("feature project is null");
			return; // TODO: error handling
		}

		addFeaturesToTree(featureProject.getFeatureModel().getRoot());
		featuresTree.redraw(); // TODO: expand the tree
	}

	/**
	 * Add the feature name as an item to the tree.
	 * 
	 * @param root
	 *            the feature to add
	 */
	private void addFeaturesToTree(Feature root) {
		TreeItem item = new TreeItem(featuresTree, SWT.NORMAL);
		item.setText(root.getName());
		item.setData(root);
		item.setExpanded(true);

		for (Feature feature : root.getChildren())
			addFeaturesToTree(feature, item);
	}

	/**
	 * Add the feature name as an item to the tree.
	 * 
	 * @param root
	 *            the feature to add
	 * @param parent
	 *            the parent item to add the feature as a child
	 */
	private void addFeaturesToTree(Feature root, TreeItem parent) {
		TreeItem item = new TreeItem(parent, SWT.NORMAL);
		item.setText(root.getName());
		item.setData(root);
		item.setExpanded(true);

		for (Feature feature : root.getChildren())
			addFeaturesToTree(feature, item);
	}

	/**
	 * Scan the tree if at least one item is checked.
	 * 
	 * @param items
	 *            All items to check (e.g. tree.getItems())
	 * @return true if at least one item is checked
	 */
	static public boolean isOneFeatureChecked(TreeItem[] items) {
		// breadth-first search
		for (TreeItem item : items) {
			if (item.getChecked())
				return true;
		}

		for (TreeItem item : items) {
			if (isOneFeatureChecked(item.getItems()))
				return true;
		}

		return false;
	}

	/**
	 * Create feature model from selected features.
	 * 
	 * @return feature model with selected features
	 */
	public FeatureModel createFeatureModel() {
		FeatureModel fm = new FeatureModel();
		createFeatureModel(fm, null, featuresTree.getItems());
		return fm;
	}

	/**
	 * Create feature model from selected features.
	 * 
	 * @param fm
	 *            feature model
	 * @param parentFeature
	 *            parent feature to add the children features. If null no parent
	 *            is used.
	 * @param items
	 *            The items from tree to check and add to feature model.
	 */
	static protected void createFeatureModel(FeatureModel fm,
			Feature parentFeature, TreeItem[] items) {
		for (TreeItem item : items) {
			if (item.getChecked()) {
				Feature f = new Feature(fm, item.getText());

				if (parentFeature == null) {
					fm.setRoot(f);
				} else {
					parentFeature.addChild(f);
				}

				createFeatureModel(fm, f, item.getItems());
			}
		}
	}

	@Override
	public void widgetSelected(SelectionEvent e) {
		if (e.detail == SWT.CHECK) {
			TreeItem item = (TreeItem) e.item;
			boolean checked = item.getChecked();
			checkItems(item, checked);
			checkPath(item.getParentItem(), checked, false);
		}

		setPageComplete(isOneFeatureChecked(featuresTree.getItems()));
	}

	@Override
	public void widgetDefaultSelected(SelectionEvent e) {
	}

	/**
	 * (un)check the item and all its children of the tree. Also (un)check the
	 * parents up to the root.
	 * 
	 * @param item
	 *            The item to (un)check (and its children + parents)
	 * @param checked
	 *            to check or uncheck
	 * @param grayed
	 *            to gray or not to gray
	 */
	static void checkPath(TreeItem item, boolean checked, boolean grayed) {
		if (item == null)
			return;
		if (grayed) {
			checked = true;
		} else {
			for (TreeItem child : item.getItems()) {
				if (child.getGrayed() || checked != child.getChecked()) {
					checked = grayed = true;
					break;
				}
			}
		}
		item.setChecked(checked);
		item.setGrayed(grayed);
		checkPath(item.getParentItem(), checked, grayed);
	}

	/**
	 * (un)check the item of the tree and all children of this item.
	 * 
	 * @param item
	 *            The item to (un)check (and its children)
	 * @param checked
	 *            to check or uncheck
	 */
	static void checkItems(TreeItem item, boolean checked) {
		item.setGrayed(false);
		item.setChecked(checked);
		for (TreeItem subItem : item.getItems()) {
			checkItems(subItem, checked);
		}
	}
}
