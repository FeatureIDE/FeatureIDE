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
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.ui.views.collaboration.editparts.ModelEditPart;

/**
 * This class is designated for search functionalities inside of the collaborations diagramm
 * It takes care of any tasks like: creating the searchbox, catching the key events, fireing the search and so on.
 * 
 * @author Christopher Kruczek
 */
public class CollaborationViewSearch {
	
	private GraphicalViewerImpl attachedViewerParent;
	private String searchBoxText;
	private Color findResultsColor;
	private Color noSearchResultsColor;
	private List<Label> extractedLabels;
	private List<Label> matchedLabels;
	private final int BEGIN_OF_VALID_ASCII_CHARS = 48;
	private final int END_OF_VALID_ASCII_CHARS = 125;
	public static class Builder{
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
		
		public CollaborationViewSearch create(){
			return new CollaborationViewSearch(this);
		}
		
	}
	
	private CollaborationViewSearch(Builder searchBuilder) {
		this.extractedLabels = new ArrayList<Label>();
		this.matchedLabels = new ArrayList<Label>();
		this.attachedViewerParent = searchBuilder.getAttachedViewerParent();
		this.searchBoxText = searchBuilder.getSearchBoxText();
		this.findResultsColor = searchBuilder.getFindResultsColor();
		this.noSearchResultsColor = searchBuilder.getNoSearchResultsColor();
		createControls();
	}
	
	private void createControls(){
		final Shell searchBoxShell = new Shell(PlatformUI.getWorkbench().getDisplay());
		searchBoxShell.setText(searchBoxText);
		searchBoxShell.setBounds(500,500, 200, 50);
		searchBoxShell.setLayout(new FillLayout());
		final Text searchTextBox = new Text(searchBoxShell,SWT.SEARCH | SWT.SINGLE | SWT.ICON_SEARCH);
		searchTextBox.addListener(SWT.Traverse,new Listener() {
			
			@Override
			public void handleEvent(Event event) {
				if(searchTextBox.getText().equalsIgnoreCase("")){
					uncolorOldLabels();
				}
				if(event.detail == SWT.TRAVERSE_RETURN){
					
					String searchText = searchTextBox.getText();
					if(searchText.equalsIgnoreCase("")){
						return;
					}
					uncolorOldLabels();
					matchedLabels.clear();
					for(Label label : extractedLabels){
						String labelText = label.getText().toLowerCase();
						if(labelText.contains(searchText) ){
							label.setBackgroundColor(findResultsColor);
							matchedLabels.add(label);
						}
					}
					
				}
				else if(event.keyCode == SWT.ESC){
					searchBoxShell.setVisible(false);
					searchTextBox.setText("");
					uncolorOldLabels();
				}
				
			}
		});
		
		attachedViewerParent.setKeyHandler(new KeyHandler() {
			
			@Override
			public boolean keyReleased(KeyEvent event) {
				if(!searchBoxShell.isVisible() && event.keyCode != SWT.ESC && 
						   event.keyCode >= BEGIN_OF_VALID_ASCII_CHARS && event.keyCode <= END_OF_VALID_ASCII_CHARS){
					searchBoxShell.setVisible(true);
					searchTextBox.setFocus();
					
				}				
				return true;
			}
		});
	}
	
	/***
	 * This function refreshs the labels which are designated for searching.
	 * It uses the given GraphicalViewerImpl and looks for labels.
	 */
	public void refreshSearchContent(){
		ModelEditPart editPart = (ModelEditPart)attachedViewerParent.getContents();
		gatherLabels(editPart.getFigure());
	}
	
	private void uncolorOldLabels(){
		if(matchedLabels.size() != 0){
			for(Label l : matchedLabels){
				l.setBackgroundColor(noSearchResultsColor);
			}
		}
	}
	
	private void gatherLabels(IFigure rootFigure)
	{
		List<Label> labels = new ArrayList<Label>();
		gatherLabels(rootFigure,labels);
		extractedLabels = new ArrayList<Label>(labels);
	}
	
	private void gatherLabels(IFigure rootFigure,List<Label> alreadyGatheredLabels){
		
		IFigure tempRootFigure = rootFigure;
		for(Object objFigure : tempRootFigure.getChildren()){
			IFigure figure = (IFigure)objFigure;
			if(!(figure instanceof Label)){
				gatherLabels(figure,alreadyGatheredLabels);
			}
			else{
				alreadyGatheredLabels.add((Label)figure);
			}
		}
	}
	
}
