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
package de.ovgu.featureide.ui.views.collaboration;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.Label;
import org.eclipse.gef.KeyHandler;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.ui.views.collaboration.editparts.ModelEditPart;

/**
 * This class is designated for search functionalities inside of the collaborations diagram It takes care of tasks like: creating the searchbox, catching the
 * key events, firing the search and so on.
 *
 * @author Christopher Kruczek
 */
public class CollaborationViewSearch {

	private final GraphicalViewerImpl attachedViewerParent;
	private SearchDialog searchDialog;
	private final String searchBoxText;
	private final Color findResultsColor;
	private final Color noSearchResultsColor;
	private List<Label> extractedLabels;
	private final List<Label> matchedLabels;

	private class SearchDialog extends org.eclipse.jface.dialogs.Dialog {

		private Text searchTextBox;
		private String searchText;
		private final String title;

		public SearchDialog(Shell parent, String title) {
			super(parent);
			setShellStyle(SWT.CLOSE | SWT.TITLE | SWT.BORDER | SWT.DIALOG_TRIM | SWT.APPLICATION_MODAL);
			setBlockOnOpen(true);
			this.title = title;
		}

		@Override
		protected void configureShell(Shell newShell) {
			super.configureShell(newShell);
			newShell.setText(title);
		}

		@Override
		protected Control createDialogArea(Composite parent) {
			final Composite container = (Composite) super.createDialogArea(parent);
			container.setLayout(new FillLayout());
			searchTextBox = new Text(container, SWT.SEARCH | SWT.SINGLE | SWT.ICON_SEARCH);
			searchTextBox.setBounds(500, 500, 200, 50);
			searchTextBox.setSelection(searchText.length());
			return container;
		}

		@Override
		protected void buttonPressed(int buttonId) {
			searchText = searchTextBox.getText();
			super.buttonPressed(buttonId);
		}

		public String getSearchText() {
			return searchText;
		}

	}

	public static class Builder {

		private GraphicalViewerImpl attachedViewerParent;
		private String searchBoxText;
		private Color findResultsColor;
		private Color noSearchResultsColor;

		public Color getNoSearchResultsColor() {
			return noSearchResultsColor;
		}

		public Builder setNoSearchResultsColor(Color noSearchResultsColor) {
			this.noSearchResultsColor = noSearchResultsColor;
			return this;
		}

		public GraphicalViewerImpl getAttachedViewerParent() {
			return attachedViewerParent;
		}

		public Builder setAttachedViewerParent(GraphicalViewerImpl attachedViewerParent) {
			this.attachedViewerParent = attachedViewerParent;
			return this;
		}

		public String getSearchBoxText() {
			return searchBoxText;
		}

		public Builder setSearchBoxText(String searchBoxText) {
			this.searchBoxText = searchBoxText;
			return this;
		}

		public Color getFindResultsColor() {
			return findResultsColor;
		}

		public Builder setFindResultsColor(Color findResultsColor) {
			this.findResultsColor = findResultsColor;
			return this;
		}

		public CollaborationViewSearch create() {
			return new CollaborationViewSearch(this);
		}

	}

	private CollaborationViewSearch(Builder searchBuilder) {
		extractedLabels = new ArrayList<Label>();
		matchedLabels = new ArrayList<Label>();
		attachedViewerParent = searchBuilder.getAttachedViewerParent();
		searchBoxText = searchBuilder.getSearchBoxText();
		findResultsColor = searchBuilder.getFindResultsColor();
		noSearchResultsColor = searchBuilder.getNoSearchResultsColor();
		createControls();
	}

	private void createControls() {

		attachedViewerParent.setKeyHandler(new KeyHandler() {

			@Override
			public boolean keyPressed(KeyEvent event) {
				if (event.keyCode == SWT.ESC) {
					uncolorOldLabels();
				} else if (((event.stateMask & SWT.CTRL) == SWT.CTRL) && (event.keyCode == 'f')) {
					if (searchDialog == null) {
						searchDialog = new SearchDialog(PlatformUI.getWorkbench().getDisplay().getActiveShell(), searchBoxText);
					}
					searchDialog.searchText = Character.toString(event.character);
					searchDialog.open();
					final String searchText = searchDialog.getSearchText();
					if (!searchText.isEmpty()) {
						uncolorOldLabels();
						matchedLabels.clear();
						for (final Label label : extractedLabels) {
							final String labelText = label.getText().toLowerCase();
							if (labelText.contains(searchText)) {
								label.setBackgroundColor(findResultsColor);
								matchedLabels.add(label);
							}
						}
					}
				}

				return true;
			}
		});
	}

	/**
	 * This function refreshes the labels which are designated for searching. It uses the given GraphicalViewerImpl and looks for labels.
	 */
	public void refreshSearchContent() {
		final ModelEditPart editPart = (ModelEditPart) attachedViewerParent.getContents();
		gatherLabels(editPart.getFigure());
	}

	private void uncolorOldLabels() {
		if (matchedLabels.size() != 0) {
			for (final Label l : matchedLabels) {
				l.setBackgroundColor(noSearchResultsColor);
			}
		}
	}

	private void gatherLabels(IFigure rootFigure) {
		final List<Label> labels = new ArrayList<Label>();
		gatherLabels(rootFigure, labels);
		extractedLabels = new ArrayList<Label>(labels);
	}

	private void gatherLabels(IFigure rootFigure, List<Label> alreadyGatheredLabels) {

		final IFigure tempRootFigure = rootFigure;
		for (final Object objFigure : tempRootFigure.getChildren()) {
			final IFigure figure = (IFigure) objFigure;
			if (!(figure instanceof Label)) {
				gatherLabels(figure, alreadyGatheredLabels);
			} else {
				alreadyGatheredLabels.add((Label) figure);
			}
		}
	}

}
