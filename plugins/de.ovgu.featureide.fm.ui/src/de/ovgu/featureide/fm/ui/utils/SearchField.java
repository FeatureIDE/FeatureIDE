/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.utils;

import java.util.Iterator;

import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * An UI text field with search functionality.
 *
 * @author Sebastian Krieter
 * @author Insansa Michel
 * @author Malek Badeer
 */
public class SearchField<T> {

	private final class SearchNextListener implements KeyListener {

		@Override
		public void keyReleased(KeyEvent e) {}

		@Override
		public void keyPressed(KeyEvent e) {
			if (e.character == 13) {
				curIndex++;
				search();
			}
		}
	}

	private final class SearchModifyListener implements ModifyListener {

		@Override
		public void modifyText(ModifyEvent e) {
			curIndex = 0;
		}
	}

	private final SearchModifyListener searchModifyListener = new SearchModifyListener();

	private final SearchNextListener searchNextListener = new SearchNextListener();

	private final Text searchField;
	private final ISearchable<T> searchable;

	private int curIndex;

	private IGraphicalFeatureModel graphicalFeatureModel = null;

	private FeatureDiagramEditor featureDiagramEditor = null;

	public SearchField(Composite parent, final ISearchable<T> searchable, FeatureDiagramEditor featureDiagramEditor) {
		this.featureDiagramEditor = featureDiagramEditor;
		graphicalFeatureModel = this.featureDiagramEditor.getGraphicalFeatureModel();
		if ((searchable == null) || (parent == null)) {
			throw new NullPointerException();
		}
		this.searchable = searchable;
		this.searchField = new Text(parent, SWT.SEARCH | SWT.ICON_SEARCH | SWT.ICON_CANCEL | SWT.BORDER);

		final GridData gridData = new GridData();
		gridData.horizontalAlignment = SWT.RIGHT;
		gridData.verticalAlignment = SWT.CENTER;
		gridData.grabExcessHorizontalSpace = true;
		gridData.widthHint = 300;
		gridData.minimumWidth = 150;

		searchField.setLayoutData(gridData);
		searchField.addModifyListener(searchModifyListener);
		searchField.addKeyListener(searchNextListener);
	}

	public SearchField(Composite parent, final ISearchable<T> searchable) {
		if ((searchable == null) || (parent == null)) {
			throw new NullPointerException();
		}
		this.searchable = searchable;
		this.searchField = new Text(parent, SWT.SEARCH | SWT.ICON_SEARCH | SWT.ICON_CANCEL | SWT.BORDER);

		final GridData gridData = new GridData();
		gridData.horizontalAlignment = SWT.RIGHT;
		gridData.verticalAlignment = SWT.CENTER;
		gridData.grabExcessHorizontalSpace = true;
		gridData.widthHint = 300;
		gridData.minimumWidth = 150;

		searchField.setLayoutData(gridData);
		searchField.addModifyListener(searchModifyListener);
		searchField.addKeyListener(searchNextListener);
	}

	private void search() {
		final String searchString = searchField.getText();
		if ((searchString == null) || searchString.isEmpty()) {
			curIndex = 0;
			return;
		}
		final Iterator<T> it = searchable.createIterator();
		int i = 0;
		T temp = null;
		int tempIndex = -1;
		for (; it.hasNext(); i++) {
			final T next = it.next();
			if (searchable.matches(next, searchString)) {
				if (i >= curIndex) {
					expand(next);
					curIndex = i;
					searchable.found(next);
					return;
				} else if (temp == null) {
					temp = next;
					tempIndex = i;
				}
			}
		}
		if (temp != null) {
			curIndex = tempIndex;
			expand(temp);
			searchable.found(temp);
		} else {
			curIndex = 0;
		}
	}

	private void expand(T next) {
		if (next instanceof IGraphicalFeature) {
			if (((IGraphicalFeature) next).getSourceConnection().getTarget() != null) {
				final IGraphicalFeature parent = ((IGraphicalFeature) next).getSourceConnection().getTarget();
				if (parent.getSourceConnection().getTarget() != null) {
					expand((T) parent);
				}
				if (parent.isCollapsed()) {
					parent.setCollapsed(false);
					if (featureDiagramEditor != null) {
						refresh();
					}
				}
			}
		}
	}

	private void refresh() {
		featureDiagramEditor.getViewer().getControl().setBackground(FMPropertyManager.getDiagramBackgroundColor());
		featureDiagramEditor.getViewer().reload();
		featureDiagramEditor.refreshGraphics(null);
		featureDiagramEditor.getViewer().refreshChildAll(FeatureUtils.getRoot(graphicalFeatureModel.getFeatureModelManager().getObject()));
		featureDiagramEditor.analyzeFeatureModel();
	}

}
