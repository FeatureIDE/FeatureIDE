/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.LineBorder;
import org.eclipse.draw2d.XYLayout;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.LegendEditPart;

/**
 * TODO represents a legend for the feature model
 * 
 * @author Fabian Benduhn
 */
public class LegendFigure extends Figure implements GUIDefaults {
	

	/**
	 * Height of each Row (should not be smaller than height of symbols)
	 */
	private static final int ROW_HEIGHT = 15;
	/**
	 * Distance between left border and label in each row (should be larger than width of biggest symbol)
	 */
	private static final int LABEL_PADDING = 30;
	/**
	 * Specific left-padding for Mandatory and Optional rows
	 */
	private static final int MANDATORY_PADDING = 12;
	/**
	 * Specific left-padding for Grouptype rows
	 */
	private static final int GROUPTYPE_PADDING = 8;
	/**
	 * Additional lift for every row except title (to adjust the space between title and second row)
	 */
	private static final int LIFT = 10;
	/**
	 * Additional lift for Mandatory and Optional rows
	 */
	private static final int MANDATORY_LIFT = 3;
	
	private final XYLayout layout = new XYLayout();
	public Point newPos;
	@Override
	public boolean useLocalCoordinates() {
		return true;

	}

	public LegendFigure(LegendEditPart part, Point pos) {
		setLocation(pos);
		setLayoutManager(layout);
		setBorder(new LineBorder(1));
		setSize(LEGEND_WIDTH,LEGEND_HEIGHT);
		createRows();
		setForegroundColor(CONNECTION_FOREGROUND);
		setBackgroundColor(DIAGRAM_BACKGROUND);
		
	}

	private void createRows() {
		createRowTitle();
		createRowMandatory();
		createRowOptional();
		createRowOr();
		createRowAlternative();
		createRowAnd();
	}

	private void createRowTitle() {
		Label labelTitle = new Label();
		labelTitle.setForegroundColor(FEATURE_FOREGROUND);
		labelTitle.setText("Legend:");
		labelTitle.setLabelAlignment(Label.LEFT);
		layout.setConstraint(labelTitle, new Rectangle(3, 0, LEGEND_WIDTH,ROW_HEIGHT));
		add(labelTitle);
	}


	private void createRowAnd() {
		Point point = new Point(GROUPTYPE_PADDING,ROW_HEIGHT*6-LIFT);
		LegendGroupTypeSymbol symbolAnd = new LegendGroupTypeSymbol(false, false,
				point,this.getLocation());
		layout.setConstraint(symbolAnd, new Rectangle(this.getLocation().x, this.getLocation().y+ROW_HEIGHT*6, symbolAnd.getPreferredSize().width, symbolAnd.getPreferredSize().height));
		Label labelAnd = new Label("And");
		labelAnd.setLabelAlignment(Label.LEFT);
		layout.setConstraint(labelAnd, new Rectangle(LABEL_PADDING, ROW_HEIGHT*6-LIFT ,LEGEND_WIDTH-LABEL_PADDING, ROW_HEIGHT));
		add(symbolAnd);
		add(labelAnd);
		labelAnd.setForegroundColor(FEATURE_FOREGROUND);
	}


	private void createRowAlternative() {
		LegendGroupTypeSymbol symbolAlternative = new LegendGroupTypeSymbol(true, false,
				new Point(GROUPTYPE_PADDING,ROW_HEIGHT*5-LIFT),this.getLocation());
		layout.setConstraint(symbolAlternative, new Rectangle(this.getLocation().x,this.getLocation().y+ROW_HEIGHT*5, symbolAlternative.getPreferredSize().width, symbolAlternative.getPreferredSize().height));
		Label labelAlternative = new Label("Alternative");
		labelAlternative.setLabelAlignment(Label.LEFT);
		layout.setConstraint(labelAlternative, new Rectangle(LABEL_PADDING, ROW_HEIGHT*5-10, LEGEND_WIDTH-LABEL_PADDING, ROW_HEIGHT));
		add(symbolAlternative);
		add(labelAlternative);
		labelAlternative.setForegroundColor(FEATURE_FOREGROUND);
	}


	private void createRowOr() {
		LegendGroupTypeSymbol symbolOr = new LegendGroupTypeSymbol(true, true,
				new Point(GROUPTYPE_PADDING,ROW_HEIGHT*4-LIFT),this.getLocation());
		layout.setConstraint(symbolOr, new Rectangle(this.getLocation().x,this.getLocation().y+ ROW_HEIGHT*4, symbolOr.getPreferredSize().width, symbolOr.getPreferredSize().height));
		Label labelOr = new Label("Or");
		labelOr.setLabelAlignment(Label.LEFT);
		layout.setConstraint(labelOr, new Rectangle(LABEL_PADDING, ROW_HEIGHT*4-LIFT, LEGEND_WIDTH-LABEL_PADDING, ROW_HEIGHT));
		add(symbolOr);
		add(labelOr);
		labelOr.setForegroundColor(FEATURE_FOREGROUND);
	}


	private void createRowOptional() {
		LegendConnectionTypeSymbol optionalSymbol = new LegendConnectionTypeSymbol(false,
				new Point(this.getLocation().x+MANDATORY_PADDING, this.getLocation().y+ROW_HEIGHT*MANDATORY_LIFT-LIFT-MANDATORY_LIFT));
		Label labelOptional = new Label("Optional");
		labelOptional.setLabelAlignment(Label.LEFT);
		layout.setConstraint(labelOptional, new Rectangle(LABEL_PADDING, ROW_HEIGHT*MANDATORY_LIFT-LIFT-MANDATORY_LIFT, LEGEND_WIDTH-LABEL_PADDING, ROW_HEIGHT));
		add(optionalSymbol);
		add(labelOptional);
		labelOptional.setForegroundColor(FEATURE_FOREGROUND);
	}


	private void createRowMandatory() {
		LegendConnectionTypeSymbol symbolMandatory = new LegendConnectionTypeSymbol(true, new Point(this.getLocation().x+MANDATORY_PADDING,this.getLocation().y+ ROW_HEIGHT*2-LIFT-MANDATORY_LIFT));
		Label labelMandatory = new Label("Mandatory");
		labelMandatory.setLabelAlignment(Label.LEFT);
		layout.setConstraint(labelMandatory, new Rectangle(LABEL_PADDING, ROW_HEIGHT*2-LIFT-MANDATORY_LIFT, LEGEND_WIDTH-LABEL_PADDING, ROW_HEIGHT));
		add(symbolMandatory);
		add(labelMandatory);
		labelMandatory.setForegroundColor(FEATURE_FOREGROUND);
	}
}
