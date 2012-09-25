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
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.PolylineConnection;
import org.eclipse.draw2d.RectangleFigure;
import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.draw2d.XYLayout;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.swt.graphics.Color;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;
import de.ovgu.featureide.fm.ui.properties.language.ILanguage;

/**
 * represents a legend for the feature model
 * 
 * @author Fabian Benduhn
 * @author Florian Proksch
 * @author Stefan Krueger
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
	/**
	 * Space between abstract/hidden/false Optional/dead features (needs some
	 * more space for the symbols)
	 */
	private static final int LIFT_2 = 12;

	private static final int SYMBOL_SIZE = ROW_HEIGHT;
	private static final String ALTERNATIVE_TOOLTIP = "Alternative group:\n\nExactly one of the features in this group must be selected.";
	private static final String OR_TOOLTIP = "Or Group:\n\nAt least one of the features in this group must be selected.";
	private static final String OPTIONAL_TOOLTIP = "Optional feature:\n\nThis feature does not have to be selected.";
	private static final String MANDATORY_TOOLTIP = "Mandatory feature:\n\nThis feature must be selected whenever its parent is selected.";
	private static final String ABSTRACT_TOOLTIP = "Abstract feature:\n\nThis feature does not contain any implementation modules,\ni.e no corresponding folder is used.";
	private static final String CONCRETE_TOOLTIP = "Concrete feature:\n\nThis feature contains implementation modules,\ni.e. a corresponding folder is used.";
	private static final String HIDDEN_TOOLTIP = "Hidden feature:\n\nThis feature will not be shown in the configuration editor.\nNon-hidden features should determine when to select the feature automatically.";
	private static final String DEAD_TOOLTIP = "Dead feature:\n\nThis feature cannot be selected in any valid configuration.";
	private static final String FALSE_OPT_TOOLTIP = "False optional feature:\n\nThis feature is declared optional but cannot be selected in any valid configuration.";
	private static final String INDET_HIDDEN_TOOLTIP = "Indeterminate hidden feature:\n\n This feature is declared hidden but does not depend on any unhidden features.";
	private static final String REDUNDANT_TOOLTIP = "Redundant constraint:\n\n This constraint does not change the product line";
	private static final String DEAD_CONST_TOOLTIP = "Dead constraint";
	private static final String UNSATISFIABLE_CONST_TOOLTIP = "Unsatisfiable Constraint\n\nThis constraint cannot become true";
	private static final String TAUTOLOGY_CONST_TOOLTIP = "Constraint is tautology\n\nThis constraint cannot become false";
	private static final String MODEL_CONST_TOOLTIP = "Constraint makes the model void";	
	
	private static final int ABSTRACT = 0;
	private static final int CONCRETE = 1;
	private static final int HIDDEN = 2;
	private static final int DEAD = 3;
	private static final int AND = 4;
	private static final int OR = 5;
	private static final int ALTERNATIVE = 6;
	private static final int FALSE_OPT = 7;

	
	private final XYLayout layout = new XYLayout();
	public Point newPos;
	private int width;
	private ILanguage language;

	@Override
	public boolean useLocalCoordinates() {
		return true;

	}

	public LegendFigure(FeatureModel featureModel, Point pos) {
		boolean mandatory = featureModel.hasMandatoryFeatures();
		boolean optional = featureModel.hasOptionalFeatures();
		boolean and = featureModel.hasAndGroup();
		boolean alternative = featureModel.hasAlternativeGroup();
		boolean or = featureModel.hasOrGroup();
		boolean abstrac = featureModel.hasAbstract();
		boolean concrete = featureModel.hasConcrete();
		boolean hidden = featureModel.hasHidden();
		boolean dead = featureModel.hasDead() ;  //same color
		boolean showHidden = featureModel.getLayout().showHiddenFeatures();
		boolean falseOpt = featureModel.hasFalse();
		boolean indetHidden = featureModel.hasIndetHidden();
		boolean unsatisfiableConst = featureModel.hasUnsatisfiableConst(); 
		boolean tautologyConst = featureModel.hasTautologyConst();
		boolean deadConst = featureModel.hasDeadConst();
		boolean voidModelConst = featureModel.hasVoidModelConst(); 
		boolean redundantConst = featureModel.hasRedundantConst();
		language = FMPropertyManager.getLanguage();
		setLocation(pos);
		setLayoutManager(layout);
		setBorder(FMPropertyManager.getLegendBorder());
		setLegendSize(mandatory, optional, or, alternative, and, abstrac,
				concrete, hidden, dead, falseOpt, showHidden, indetHidden,
				unsatisfiableConst, tautologyConst, deadConst,  voidModelConst, redundantConst);
		FeatureUIHelper.setLegendSize(featureModel,this.getSize());
		FeatureUIHelper.setLegendFigure(featureModel,this);
		createRows(mandatory, optional, or, alternative, and, abstrac,
				concrete, hidden, dead, falseOpt, showHidden, indetHidden,
				unsatisfiableConst, tautologyConst, deadConst, voidModelConst, redundantConst);
		setForegroundColor(FMPropertyManager.getLegendForgroundColor());
		setBackgroundColor(FMPropertyManager.getLegendBackgroundColor());
		this.width = LEGEND_WIDTH;
		this.setOpaque(true);
	}

	/**
	 * 
	 * @param mandatory
	 * @param optional
	 * @param or
	 * @param alternative
	 * @param and
	 * @param _abstract
	 * @param concrete
	 * @param hidden
	 * @param dead
	 * @param falseOpt
	 * @param showHidden
	 * @param indetHidden
	 * @param unsatisfiableConst
	 * @param tautologyConst
	 * @param deadConst
	 * @param voidModelConst
	 * @param redundantConst
	 */
	private void setLegendSize(boolean mandatory, boolean optional, boolean or,
			boolean alternative, boolean and, boolean _abstract,
			boolean concrete, boolean hidden, boolean dead, boolean falseOpt, boolean showHidden, boolean indetHidden,
			boolean unsatisfiableConst, boolean tautologyConst, boolean deadConst, boolean voidModelConst, boolean redundantConst) {
		int height = ROW_HEIGHT * 2 - 5;
		if (mandatory)
			height = height + ROW_HEIGHT;
		if (optional)
			height = height + ROW_HEIGHT;
		if (or)
			height = height + ROW_HEIGHT;
		if (alternative)
			height = height + ROW_HEIGHT;
		// if (and)
		// height = height + ROW_HEIGHT;
		if (_abstract && concrete) {
			height = height + ROW_HEIGHT;
			height = height + ROW_HEIGHT;
		}
		if (hidden && showHidden)
			height = height + ROW_HEIGHT;
		if (dead)
			height = height + ROW_HEIGHT;
		if (deadConst)
			height = height + ROW_HEIGHT;
		if (falseOpt)	
		{
			height = height + ROW_HEIGHT;
		}
		if (showHidden && indetHidden)
		{
			height = height + ROW_HEIGHT;
		}
		if (tautologyConst)	
		{
			height = height + ROW_HEIGHT;
		}
		if (unsatisfiableConst)
		{
			height = height + ROW_HEIGHT;
		}
		
		if (voidModelConst)	
		{
			height = height + ROW_HEIGHT;
		}
		if (redundantConst)
		{
			height = height + ROW_HEIGHT;
		}
		
		
		width = LEGEND_WIDTH;
		if (!mandatory && !alternative && !dead) {
			if (!optional && !concrete && !_abstract) {
				width = 50;
			} else {
				width = 80;
			}
		} else if (dead) {
			width = 160;
		}else if (indetHidden || unsatisfiableConst || deadConst  || redundantConst || voidModelConst || tautologyConst)
		{
			width = 170;
		}
			
		this.setSize(width, height);
	}

	private void createRows(boolean mandatory, boolean optional, boolean or,
			boolean alternative, boolean and, boolean abstrac,
			boolean concrete, boolean hidden, boolean dead, boolean falseoptional, boolean showHidden, boolean indetHidden,
			boolean unsatisfiableConst, boolean tautologyConst, boolean deadConst, boolean voidModelConst, boolean redundantConst) {
		
		boolean yellowShown = false, redShown = false;;
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
		// if (and)
		// createRowAnd(row);
		if (abstrac && concrete) {
			createRowAbstract(row++);
			createRowConcrete(row++);
		}
		if (hidden && showHidden)
			createRowHidden(row++);
		if (dead)
		{
			createRowDead(row++, redShown);
			redShown = true;
		}
		if (deadConst)
		{
			createRowDeadConst(row++, redShown);
			redShown = true;
		}		
		
		if (voidModelConst)
		{			
			createRowVoidModelConst(row++, redShown);
			redShown = true;
		}
		
		if (unsatisfiableConst)
		{			
			createRowUnsatisfiableConst(row++, redShown);
			redShown = true;
		}
		
		//Yellow lines must be after one another
		if (falseoptional)
        {
        	//createRowFalseOpt(yellowShown ? row : row++, yellowShown);
        	createRowFalseOpt(row++, yellowShown);
        	yellowShown = true;
        }
		if (showHidden && indetHidden)
		{
			createRowIndetHidden(row++, yellowShown);
			yellowShown = true;
		}
		if (redundantConst)
		{			
			createRowRedundantConst(row++, yellowShown);
			yellowShown = true;
		}

		if (tautologyConst)
		{			
			createRowTautologyConst(row++, yellowShown);
			yellowShown = true;
		}		
		
	}

	private void createRowRedundantConst(int row, boolean drawBox) {
		createSymbol(row, FALSE_OPT, drawBox);
		Label labelIndetHidden = createLabel(row, language.getRedundantConst(),
				FMPropertyManager.getFeatureForgroundColor(), REDUNDANT_TOOLTIP);
		add(labelIndetHidden);		
	}	
	
	private void createRowDeadConst(int row, boolean drawBox) {
		createSymbol(row, DEAD, drawBox);
		Label labelIndetHidden = createLabel(row, language.getDeadConst(),
				FMPropertyManager.getFeatureForgroundColor(), DEAD_CONST_TOOLTIP);
		add(labelIndetHidden);		
	}	
	
	private void createRowUnsatisfiableConst(int row, boolean drawBox) {
		createSymbol(row, DEAD, drawBox);
		Label labelIndetHidden = createLabel(row, language.getUnsatisfiableConst(),
				FMPropertyManager.getFeatureForgroundColor(), UNSATISFIABLE_CONST_TOOLTIP);
		add(labelIndetHidden);		
	}	
	
	private void createRowTautologyConst(int row, boolean drawBox) {
		createSymbol(row, FALSE_OPT, drawBox);
		Label labelIndetHidden = createLabel(row, language.getTautologyConst(),
				FMPropertyManager.getFeatureForgroundColor(), TAUTOLOGY_CONST_TOOLTIP);
		add(labelIndetHidden);		
	}	

	private void createRowVoidModelConst(int row, boolean drawBox) {
		createSymbol(row, DEAD, drawBox);
		Label labelIndetHidden = createLabel(row, language.getVoidModelConst(),
				FMPropertyManager.getFeatureForgroundColor(), MODEL_CONST_TOOLTIP);
		add(labelIndetHidden);		
	}	

	private void createRowIndetHidden(int row, boolean drawBox) {
		createSymbol(row, FALSE_OPT, drawBox);
		Label labelIndetHidden = createLabel(row, language.getIndetHidden(),
				FMPropertyManager.getFeatureForgroundColor(), INDET_HIDDEN_TOOLTIP);
		add(labelIndetHidden);		
	}
	
	
	private void createRowFalseOpt(int row, boolean drawBox) {
		createSymbol(row, FALSE_OPT, drawBox);
		Label labelFalseOpt = createLabel(row, language.getFalseOptional(),
				FMPropertyManager.getFeatureForgroundColor(), FALSE_OPT_TOOLTIP);
		add(labelFalseOpt);

		
	}

	private void createRowTitle() {
		Label labelTitle = new Label();
		labelTitle.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		labelTitle.setFont(DEFAULT_FONT);
		labelTitle.setText(language.getLagendTitle());
		labelTitle.setLabelAlignment(Label.LEFT);
		layout.setConstraint(labelTitle, new Rectangle(3, 0, width, ROW_HEIGHT));
		add(labelTitle);
	}

	// private void createRowAnd(int row, AND) {
	// createGroupTypeSymbol(row, false, false);
	// Label labelOr = createLabel(row, "And");
	// add(labelOr);
	// labelOr.setForegroundColor(FEATURE_FOREGROUND);
	// }

	private void createRowAlternative(int row) {
		createGroupTypeSymbol(row, ALTERNATIVE);
		Label labelOr = createLabel(row, language.getAlternative(), FMPropertyManager.getFeatureForgroundColor(),
				ALTERNATIVE_TOOLTIP);

		add(labelOr);
	}

	private void createRowOr(int row) {
		createGroupTypeSymbol(row, OR);
		Label labelOr = createLabel(row, language.getOr(), FMPropertyManager.getFeatureForgroundColor(), OR_TOOLTIP);
		add(labelOr);
	}

	private void createRowOptional(int row) {
		PolylineConnection p = createConnectionTypeSymbol(row, false);
		add(p);
		Label labelMandatory = createLabel(row, language.getOptional(), FMPropertyManager.getFeatureForgroundColor(),
				OPTIONAL_TOOLTIP);
		add(labelMandatory);
	}

	private void createRowMandatory(int row) {

		PolylineConnection p = createConnectionTypeSymbol(row, true);
		add(p);
		Label labelMandatory = createLabel(row, language.getMandatory(),
				FMPropertyManager.getFeatureForgroundColor(), MANDATORY_TOOLTIP);
		add(labelMandatory);

	}

	private void createRowAbstract(int row) {

		createSymbol(row, ABSTRACT);
		Label labelAbstract = createLabel(row, language.getAbstract(), FMPropertyManager.getFeatureForgroundColor(),
				ABSTRACT_TOOLTIP);
		add(labelAbstract);

	}

	private void createRowConcrete(int row) {

		createSymbol(row, CONCRETE);
		Label labelConcrete = createLabel(row, language.getConcrete(), FMPropertyManager.getFeatureForgroundColor(),
				CONCRETE_TOOLTIP);
		add(labelConcrete);

	}

	private void createRowHidden(int row) {

		createSymbol(row, HIDDEN);
		Label labelHidden = createLabel(row, language.getHidden(), HIDDEN_FOREGROUND,
				HIDDEN_TOOLTIP);
		add(labelHidden);

	}

	private void createRowDead(int row, boolean drawBox) {
		createSymbol(row, DEAD, drawBox);
		Label labelDead = createLabel(row, language.getDead(),
				FMPropertyManager.getFeatureForgroundColor(), DEAD_TOOLTIP);
		add(labelDead);

	}

	private Label createLabel(int row, String text, Color foreground,
			String tooltip) {
		Label label = new Label(text);
		label.setLabelAlignment(Label.LEFT);
		layout.setConstraint(label, new Rectangle(LABEL_PADDING, ROW_HEIGHT
				* row - LIFT, width - LABEL_PADDING, ROW_HEIGHT));
		label.setForegroundColor(foreground);
		label.setBackgroundColor(FMPropertyManager.getDiagramBackgroundColor());
		label.setFont(DEFAULT_FONT);
		label.setToolTip(createToolTipContent(tooltip));
		return label;
	}

	/**
	 * @param text
	 * @return
	 */
	private Figure createToolTipContent(String text) {
		Figure toolTipContent = new Figure();
		toolTipContent.setLayoutManager(new GridLayout());
		toolTipContent.add(new Label(text));
		return toolTipContent;
	}

	/**
	 * 
	 * @param row
	 *            the row in which the group type symbol shall appear
	 * @param type
	 *            AND, OR, ALTERNATIVE
	 */
	private void createGroupTypeSymbol(int row, int type) {
		boolean fill = true;
		boolean decoration = true;
		String toolTipText="";
		if (type == AND) {
			
			fill = false;
		} else if (type == OR) {
			toolTipText = OR_TOOLTIP;
			fill = true;
			decoration = true;
		} else {
			toolTipText=ALTERNATIVE_TOOLTIP;
			fill = false;
			decoration = true;
		}
		// otherwise type must be ALTERNATIVE and decoration = false;

		Point p1 = new Point(GROUPTYPE_PADDING + SYMBOL_SIZE, ROW_HEIGHT * row
				+ SYMBOL_SIZE - LIFT);
		Point p2 = new Point((GROUPTYPE_PADDING + SYMBOL_SIZE / 2), ROW_HEIGHT
				* row - LIFT);
		Point p3 = new Point(GROUPTYPE_PADDING, ROW_HEIGHT * row + SYMBOL_SIZE
				- LIFT);

		RotatableDecoration sourceDecoration = new LegendRelationDecoration(
				fill, p1);
		PolylineConnection line = new PolylineConnection();
		line.setForegroundColor(FMPropertyManager.getConnectionForgroundColor());

		line.setEndpoints(p2, p3);

		if (decoration)
			line.setSourceDecoration(sourceDecoration);
		PolylineConnection line2 = new PolylineConnection();
		line2.setForegroundColor(FMPropertyManager.getConnectionForgroundColor());

		line2.setEndpoints(p2, p1);
		this.add(line);
		this.add(line2);
		Figure toolTipContent = createToolTipContent(toolTipText);
		line.setToolTip(toolTipContent);
		line2.setToolTip(toolTipContent);
		setForegroundColor(FMPropertyManager.getConnectionForgroundColor());

	}

	private PolylineConnection createConnectionTypeSymbol(int row,
			boolean mandatory) {

		PolylineConnection p = new PolylineConnection();
		p.setForegroundColor(FMPropertyManager.getConnectionForgroundColor());
		p.setSourceDecoration(new CircleDecoration(mandatory));

		Point source = new Point(MANDATORY_PADDING, ROW_HEIGHT * row - LIFT
				+ SYMBOL_SIZE / 2);

		Point target = new Point(MANDATORY_PADDING + SYMBOL_SIZE / 2, row
				* ROW_HEIGHT - LIFT);

		p.setEndpoints(source, target);
		String toolTipText;
		if (mandatory)
			toolTipText = MANDATORY_TOOLTIP;
		else
			toolTipText = OPTIONAL_TOOLTIP;
		p.setToolTip(createToolTipContent(toolTipText));
		return p;
	}

	private void createSymbol(int row, int type) 
	{
		createSymbol( row, type, false);
	}		
	
	private void createSymbol(int row, int type, boolean drawNoBox) {
		int x1 = (SYMBOL_SIZE / 2 - 2);
		int y1 = (ROW_HEIGHT * row - LIFT_2 / 2);
		int x2 = SYMBOL_SIZE + SYMBOL_SIZE / 2;
		int y2 = (ROW_HEIGHT * row + SYMBOL_SIZE - LIFT_2);
		Point p1 = new Point(x1, y1);

		Figure rect = new RectangleFigure();
		String toolTipText = "";
		switch (type) {

		case (ABSTRACT):
			rect.setBorder(FMPropertyManager.getAbsteactFeatureBorder(false));
			rect.setBackgroundColor(FMPropertyManager.getAbstractFeatureBackgroundColor());
			toolTipText = ABSTRACT_TOOLTIP;
			break;
		case (CONCRETE):
			rect.setBorder(FMPropertyManager.getConcreteFeatureBorder(false));
			rect.setBackgroundColor(FMPropertyManager.getConcreteFeatureBackgroundColor());
			toolTipText = CONCRETE_TOOLTIP;
			break;
		case (HIDDEN):
			rect.setBorder(FMPropertyManager.getHiddenLegendBorder());
			toolTipText = HIDDEN_TOOLTIP;
			break;
		case (DEAD):
			rect.setBorder(FMPropertyManager.getDeadFeatureBorder(false));
			rect.setBackgroundColor(FMPropertyManager.getDeadFeatureBackgroundColor());
			toolTipText = DEAD_TOOLTIP;
			break;
	    case (FALSE_OPT):
	    	rect.setBorder(FMPropertyManager.getConcreteFeatureBorder(false));
			rect.setBackgroundColor(FMPropertyManager.getWarningColor());
			toolTipText = FALSE_OPT_TOOLTIP;
			break;
	 	}
		rect.setSize(x2 - x1, y2 - y1);
		rect.setLocation(p1);
		rect.setToolTip(createToolTipContent(toolTipText));
		if (!drawNoBox) this.add(rect);
	}
}
