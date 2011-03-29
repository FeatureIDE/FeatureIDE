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
import org.eclipse.draw2d.PolylineConnection;
import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.draw2d.XYLayout;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;

import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

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
	 * Distance between left border and label in each row (should be larger than
	 * width of biggest symbol)
	 */
	private static final int LABEL_PADDING = 30;
	/**
	 * Specific left-padding for Mandatory and Optional rows
	 */
	private static final int MANDATORY_PADDING = 12;
	/**
	 * Specific left-padding for Grouptype rows
	 */
	private static final int GROUPTYPE_PADDING = 5;
	/**
	 * Additional lift for every row except title (to adjust the space between
	 * title and second row)
	 */
	private static final int LIFT = 10;

	private static final int SYMBOL_SIZE = ROW_HEIGHT;

	private final XYLayout layout = new XYLayout();
	public Point newPos;

	@Override
	public boolean useLocalCoordinates() {
		return true;

	}

	public LegendFigure(Point pos, boolean mandatory, boolean optional,
			boolean or, boolean alternative, boolean and) {
		setLocation(pos);
		setLayoutManager(layout);
		setBorder(new LineBorder(1));
		setLegendSize(mandatory, optional, or, alternative, and);
		FeatureUIHelper.setLegendSize(this.getSize());
		FeatureUIHelper.setLegendFigure(this);
		createRows(mandatory, optional, or, alternative, and);
		setForegroundColor(CONNECTION_FOREGROUND);
		setBackgroundColor(DIAGRAM_BACKGROUND);

	}

	/**
	 * @param mandatory
	 * @param optional
	 * @param or
	 * @param alternative
	 * @param and
	 * @return
	 */
	private void setLegendSize(boolean mandatory, boolean optional, boolean or,
			boolean alternative, boolean and) {
		int height = ROW_HEIGHT * 2 - 5;
		if (mandatory)
			height = height + ROW_HEIGHT;
		if (optional)
			height = height + ROW_HEIGHT;
		if (or)
			height = height + ROW_HEIGHT;
		if (alternative)
			height = height + ROW_HEIGHT;
		if (and)
			height = height + ROW_HEIGHT;

		int width = LEGEND_WIDTH;
		if (!mandatory && !alternative) {
			if (!optional) {
				width = 50;
			} else {
				width = 80;
			}
		}
		this.setSize(width, height);
	}

	private void createRows(boolean mandatory, boolean optional, boolean or,
			boolean alternative, boolean and) {

		createRowTitle();
		int row = 2;
		if (mandatory)
			createRowMandatory(row++);
		if (optional)
			createRowOptional(row++);
		if (or)
			createRowOr(row++);
		if (alternative)
			createRowAlternative(row++);
		if (and)
			createRowAnd(row);
	}

	private void createRowTitle() {
		Label labelTitle = new Label();
		labelTitle.setForegroundColor(FEATURE_FOREGROUND);
		labelTitle.setText("Legend:");
		labelTitle.setLabelAlignment(Label.LEFT);
		layout.setConstraint(labelTitle, new Rectangle(3, 0, LEGEND_WIDTH,
				ROW_HEIGHT));
		add(labelTitle);
	}

	private void createRowAnd(int row) {
		createGroupTypeSymbol(row, false, false);
		Label labelOr = createLabel(row, "And");
		add(labelOr);
		labelOr.setForegroundColor(FEATURE_FOREGROUND);
	}

	private void createRowAlternative(int row) {
		createGroupTypeSymbol(row, false, true);
		Label labelOr = createLabel(row, "Alternative");
		add(labelOr);
		labelOr.setForegroundColor(FEATURE_FOREGROUND);
	}

	private void createRowOr(int row) {
		createGroupTypeSymbol(row, true, true);
		Label labelOr = createLabel(row, "Or");
		add(labelOr);
		labelOr.setForegroundColor(FEATURE_FOREGROUND);
	}

	private void createRowOptional(int row) {
		PolylineConnection p = createConnectionTypeSymbol(row, false);
		add(p);
		Label labelMandatory = createLabel(row, "Optional");
		add(labelMandatory);
	}

	private void createRowMandatory(int row) {

		PolylineConnection p = createConnectionTypeSymbol(row, true);
		add(p);
		Label labelMandatory = createLabel(row, "Mandatory");
		add(labelMandatory);

	}

	private Label createLabel(int row, String text) {
		Label label = new Label(text);
		label.setLabelAlignment(Label.LEFT);
		layout.setConstraint(label, new Rectangle(LABEL_PADDING, ROW_HEIGHT
				* row - LIFT, LEGEND_WIDTH - LABEL_PADDING, ROW_HEIGHT));
		label.setForegroundColor(FEATURE_FOREGROUND);
		return label;
	}

	/**
	 * @param decoration
	 *            if false, symbol will be of type: And
	 * @param fill
	 *            if decoration is true, symbol will be of type: Or. Otherwise
	 *            Alternative. Ignored if decoration is false;
	 */
	private void createGroupTypeSymbol(int row, boolean fill, boolean decoration) {

		Point p1 = new Point(GROUPTYPE_PADDING + SYMBOL_SIZE, ROW_HEIGHT * row
				+ SYMBOL_SIZE - LIFT);
		Point p2 = new Point((GROUPTYPE_PADDING + SYMBOL_SIZE / 2), ROW_HEIGHT
				* row - LIFT);
		Point p3 = new Point(GROUPTYPE_PADDING, ROW_HEIGHT * row + SYMBOL_SIZE
				- LIFT);

		RotatableDecoration sourceDecoration = new LegendRelationDecoration(
				fill, p1);
		PolylineConnection line = new PolylineConnection();

		line.setEndpoints(p2, p3);

		if (decoration)
			line.setSourceDecoration(sourceDecoration);
		PolylineConnection line2 = new PolylineConnection();

		line2.setEndpoints(p2, p1);
		this.add(line);
		this.add(line2);

		setForegroundColor(CONNECTION_FOREGROUND);

	}

	private PolylineConnection createConnectionTypeSymbol(int row,
			boolean mandatory) {
		PolylineConnection p = new PolylineConnection();
		p.setForegroundColor(CONNECTION_FOREGROUND);
		p.setSourceDecoration(new CircleDecoration(mandatory));
		Point source = new Point(MANDATORY_PADDING, ROW_HEIGHT * row - LIFT
				+ SYMBOL_SIZE / 2);

		Point target = new Point(MANDATORY_PADDING + SYMBOL_SIZE / 2, row
				* ROW_HEIGHT - LIFT);

		p.setEndpoints(source, target);
		return p;
	}
}
