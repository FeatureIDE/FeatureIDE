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
package de.ovgu.featureide.fm.ui.editors.featuremodel.figures;

import java.util.List;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.GridLayout;
import org.eclipse.draw2d.Label;
import org.eclipse.draw2d.PolylineConnection;
import org.eclipse.draw2d.PositionConstants;
import org.eclipse.draw2d.RectangleFigure;
import org.eclipse.draw2d.RotatableDecoration;
import org.eclipse.draw2d.XYLayout;
import org.eclipse.draw2d.geometry.Point;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.swt.graphics.Color;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelStructure;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.IGraphicalConstraint;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.filters.AbstractGraphicalFeatureFilter;
import de.ovgu.featureide.fm.ui.editors.featuremodel.filters.AlternativeGroupFilter;
import de.ovgu.featureide.fm.ui.editors.featuremodel.filters.ConcreteGraphicalFeatureFilter;
import de.ovgu.featureide.fm.ui.editors.featuremodel.filters.HiddenGraphicalFeatureFilter;
import de.ovgu.featureide.fm.ui.editors.featuremodel.filters.MandatoryGraphicalFeatureFilter;
import de.ovgu.featureide.fm.ui.editors.featuremodel.filters.OptionalGraphicalFeatureFilter;
import de.ovgu.featureide.fm.ui.editors.featuremodel.filters.OrGroupFilter;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;
import de.ovgu.featureide.fm.ui.properties.language.ILanguage;

/**
 * Represents a legend for the feature model.
 *
 * @author Fabian Benduhn
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Marcus Pinnecke
 */
public class LegendFigure extends Figure implements GUIDefaults {

	/**
	 * Height of each Row (should not be smaller than height of symbols)
	 */
	private static final int ROW_HEIGHT = 17;
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
	private static final int GROUPTYPE_PADDING = 5;
	/**
	 * Additional lift for every row except title (to adjust the space between title and second row)
	 */
	private static final int LIFT = 10;
	/**
	 * Space between abstract/hidden/false Optional/dead features (needs some more space for the symbols)
	 */
	private static final int LIFT_2 = 12;
	/**
	 * Width that the two color gradient needs to display itself
	 */
	private static final int GRADIENT_WIDTH = 250;

	private static final int SYMBOL_SIZE = ROW_HEIGHT;
	private static final String ALTERNATIVE_TOOLTIP =
		"Alternative group:\n\nExactly one of the features in this group must be selected,\n if the parent feature is selected.";
	private static final String OR_TOOLTIP = "Or Group:\n\nAt least one of the features in this group must be selected,\n if the parent feature is selected.";
	private static final String OPTIONAL_TOOLTIP = "Optional feature:\n\nThis feature does not have to be selected.";
	private static final String MANDATORY_TOOLTIP = "Mandatory feature:\n\nThis feature must be selected whenever its parent is selected.";
	private static final String ABSTRACT_TOOLTIP = "Abstract feature:\n\nThis feature does not have any impact at implementation level.";
	private static final String IMPORTED_TOOLTIP = "Imported feature:\n\nThis feature is imported from another feature model.";
	private static final String INHERITED_TOOLTIP = "Inherited feature:\n\nThis feature is inherited from a parent feature model.";
	private static final String INTERFACED_TOOLTIP = "Interface feature:\n\nThis feature is a feature from an interface.";
	private static final String CONCRETE_TOOLTIP = "Concrete feature:\n\nThis feature has impact at implementation level.";
	private static final String HIDDEN_TOOLTIP =
		"Hidden feature:\n\nThis feature will not be shown in the configuration editor.\n Non-hidden features should determine when to select the feature automatically.";
	private static final String COLLAPSED_TOOLTIP = "Collapsed feature:\n\nThe features under this parent will not be shown in the feature model editor.";
	private static final String DEAD_TOOLTIP = "Dead feature:\n\nThis feature cannot be selected in any valid configuration.";
	private static final String FALSE_OPT_TOOLTIP =
		"False optional feature:\n\nThis feature is declared optional, but is always selected\n if the parent feature is selected.";
	private static final String INDET_HIDDEN_TOOLTIP =
		"Indeterminate hidden feature:\n\n This feature is declared hidden, but does not depend on any unhidden features.";
	private static final String REDUNDANT_TOOLTIP = "Redundant constraint:\n\n This constraint does not change the product line.";
	private static final String TAUTOLOGY_CONST_TOOLTIP = "Constraint is tautology\n\n This constraint cannot become false.";
	private static final String MODEL_CONST_TOOLTIP = StringTable.FEATURE_MODELIS_VOID;
	private static final String IMPLICIT_TOOLTIP = "Implicit constraint:\n\n This constraint is an implicit dependency of the feature model.";
	private static final String EXPLANATION_TOOLTIP = "Placeholder";

	private static final int ABSTRACT = 0;
	private static final int CONCRETE = 1;
	private static final int HIDDEN = 2;
	private static final int DEAD = 3;
	private static final int AND = 4;
	private static final int OR = 5;
	private static final int ALTERNATIVE = 6;
	private static final int FALSE_OPT = 7;
	private static final int IMPORTED = 8;
	private static final int INHERITED = 9;
	private static final int INTERFACED = 10;
	private static final int IMPLICIT = 11;
	private static final int EXPLANATION = 12;
	private static final int REDUNDANT = 13;
	private static final int VOID_MODEL = 14;

	private static final XYLayout layout = new XYLayout();

	public Point newPos;
	private int width;
	private ILanguage language;
	private boolean mandatory;
	private boolean optional;
	private boolean alternative;
	private boolean or;
	private boolean _abstract;
	private boolean concrete;
	private boolean hidden;
	private boolean collapsed;
	private boolean dead;
	private boolean showHidden;
	private boolean falseoptional;
	private boolean indetHidden;
	private boolean tautologyConst;
	private boolean redundantConst;
	private boolean explanations;
	private boolean void_model;
	private boolean imported = false;
	private boolean inherited = false;
	private boolean interfaced = false;
	private boolean implicitConst = false;

	private int row;
	final IGraphicalFeatureModel graphicalFeatureModel;

	@Override
	public boolean useLocalCoordinates() {
		return true;
	}

	public LegendFigure(IGraphicalFeatureModel graphicalFeatureModel, Point pos) {
		this.graphicalFeatureModel = graphicalFeatureModel;
		final IFeatureModel featureModel = graphicalFeatureModel.getFeatureModel();

		// Set the properties that should be drawn
		refreshProperties(featureModel);

		setLocation(pos);
		setLayoutManager(layout);
		setBorder(FMPropertyManager.getLegendBorder());
		setLegendSize();
		createRows();
		setForegroundColor(FMPropertyManager.getLegendForgroundColor());
		setBackgroundColor(FMPropertyManager.getLegendBackgroundColor());
		setOpaque(true);
	}

	private void refreshProperties(IFeatureModel featureModel) {
		final FeatureModelAnalyzer analyser = featureModel.getAnalyser();

		final IFeatureModelStructure fmStructure = featureModel.getStructure();
		showHidden = graphicalFeatureModel.getLayout().showHiddenFeatures();
		fmStructure.setShowHiddenFeatures(showHidden);

		mandatory = Functional.toList(Functional.filter(graphicalFeatureModel.getVisibleFeatures(), new MandatoryGraphicalFeatureFilter())).size() > 0;
		optional = Functional.toList(Functional.filter(graphicalFeatureModel.getVisibleFeatures(), new OptionalGraphicalFeatureFilter())).size() > 0;
		alternative = Functional.toList(Functional.filter(graphicalFeatureModel.getVisibleFeatures(), new AlternativeGroupFilter())).size() > 0;
		or = Functional.toList(Functional.filter(graphicalFeatureModel.getVisibleFeatures(), new OrGroupFilter())).size() > 0;
		_abstract = Functional.toList(Functional.filter(graphicalFeatureModel.getVisibleFeatures(), new AbstractGraphicalFeatureFilter())).size() > 0;
		concrete = Functional.toList(Functional.filter(graphicalFeatureModel.getVisibleFeatures(), new ConcreteGraphicalFeatureFilter())).size() > 0;
		hidden = Functional.toList(Functional.filter(graphicalFeatureModel.getVisibleFeatures(), new HiddenGraphicalFeatureFilter())).size() > 0;

		collapsed = graphicalFeatureModel.getVisibleFeatures().size() != graphicalFeatureModel.getFeatures().size();
		if (analyser.calculateDeadConstraints) {
			dead = fmStructure.hasDeadFeatures();
		}
		if (analyser.calculateFOConstraints) {
			falseoptional = fmStructure.hasFalseOptionalFeatures();
		}
		indetHidden = fmStructure.hasIndetHidden();

		void_model = !analyser.valid();
		if (void_model) {
			dead = false;
		}

		tautologyConst = analyser.calculateTautologyConstraints && FeatureUtils.hasTautologyConst(featureModel);
		redundantConst = analyser.calculateRedundantConstraints && FeatureUtils.hasRedundantConst(featureModel);
		implicitConst = isImplicit(graphicalFeatureModel);

		explanations = graphicalFeatureModel.getActiveExplanation() != null ? true : false;

		if (featureModel instanceof ExtendedFeatureModel) {
			final ExtendedFeatureModel extendedFeatureModel = (ExtendedFeatureModel) featureModel;
			interfaced = extendedFeatureModel.hasInterface();
			// interfaces hide other features
			imported = !interfaced && extendedFeatureModel.hasInstance();
			inherited = !interfaced && extendedFeatureModel.hasInherited();
		}

		language = FMPropertyManager.getLanguage();
	}

	private void setLegendSize() {
		width = LEGEND_WIDTH;
		int height = ROW_HEIGHT * 2;
		if (mandatory) {
			height = height + ROW_HEIGHT;
			setWidth(language.getMandatory());
		}
		if (optional) {
			height = height + ROW_HEIGHT;
			setWidth(language.getOptional());
		}
		if (or) {
			height = height + ROW_HEIGHT;
			setWidth(language.getOptional());
		}
		if (alternative) {
			height = height + ROW_HEIGHT;
			setWidth(language.getAlternative());
		}
		if (_abstract) {
			height = height + ROW_HEIGHT;
			setWidth(language.getAbstract());
		}
		if (concrete) {
			height = height + ROW_HEIGHT;
			setWidth(language.getConcrete());
		}
		if (imported) {
			height = height + ROW_HEIGHT;
			setWidth(language.getImported());
		}
		if (inherited) {
			height = height + ROW_HEIGHT;
			setWidth(language.getInherited());
		}
		if (interfaced) {
			height = height + ROW_HEIGHT;
			setWidth(language.getInterfaced());
		}
		if (hidden && showHidden) {
			height = height + ROW_HEIGHT;
			setWidth(language.getHidden());
		}
		if (collapsed) {
			height = height + ROW_HEIGHT;
			setWidth(language.getCollapsed());
		}
		if (dead) {
			height = height + ROW_HEIGHT;
			setWidth(language.getDead());
		}
		if (falseoptional) {
			height = height + ROW_HEIGHT;
			setWidth(language.getFalseOptional());
		}
		if (showHidden && indetHidden) {
			height = height + ROW_HEIGHT;
			setWidth(language.getIndetHidden());
		}
		if (tautologyConst) {
			height = height + ROW_HEIGHT;
			setWidth(language.getTautologyConst());
		}
		if (redundantConst) {
			height = height + ROW_HEIGHT;
			setWidth(language.getRedundantConst());
		}
		if (implicitConst) {
			height = height + ROW_HEIGHT;
			setWidth(language.getRedundantConst());
		}
		if (void_model) {
			height = height + ROW_HEIGHT;
			setWidth(language.getVoidModelConst());
		}
		this.setSize(width, height);
	}

	private void setWidth(String string) {
		final int widthInPixels = createLabel(1, string, FMPropertyManager.getFeatureForgroundColor(), "").getPreferredSize().width + 40;
		if (widthInPixels > width) {
			width = widthInPixels;
		}
	}

	private boolean isImplicit(IGraphicalFeatureModel fm) {
		final List<IGraphicalConstraint> consts = fm.getConstraints();
		for (final IGraphicalConstraint c : consts) {
			if (c.isImplicit()) {
				return true;
			}
		}
		return false;
	}

	private void createRows() {
		createRowTitle();
		row = 2;
		if (mandatory) {
			createRowMandatory(row++);
		}
		if (optional) {
			createRowOptional(row++);
		}
		if (or) {
			createRowOr(row++);
		}
		if (alternative) {
			createRowAlternative(row++);
		}
		if (_abstract) {
			createRowAbstract(row++);
		}
		if (concrete) {
			createRowConcrete(row++);
		}
		if (imported) {
			createRowImported(row++);
		}
		if (inherited) {
			createRowInherited(row++);
		}
		if (interfaced) {
			createRowInterfaced(row++);
		}
		if (hidden && showHidden) {
			createRowHidden(row++);
		}
		if (collapsed) {
			createRowCollapsed(row++);
		}
		if (dead) {
			createRowDead(row++);
		}

		if (falseoptional) {
			createRowFalseOpt(row++);
		}
		if (showHidden && indetHidden) {
			createRowIndetHidden(row++);
		}
		if (redundantConst) {
			createRowRedundantConst(row++);
		}
		if (tautologyConst) {
			createRowTautologyConst(row++);
		}
		if (implicitConst) {
			createRowImplicitConst(row++);
		}
		if (void_model) {
			createHasVoidModel(row++);
		}
		if (explanations) {
			// Explanation should be created at last
			createExplanationEntry();
		}
	}

	/**
	 * @param i
	 */
	private void createHasVoidModel(int row) {
		createSymbol(row, VOID_MODEL, true, MODEL_CONST_TOOLTIP);
		final Label labelIndetHidden = createLabel(row, language.getVoidModel(), FMPropertyManager.getFeatureForgroundColor(), MODEL_CONST_TOOLTIP);
		add(labelIndetHidden);
	}

	private void createRowRedundantConst(int row) {
		createSymbol(row, REDUNDANT, false, REDUNDANT_TOOLTIP);
		final Label labelIndetHidden = createLabel(row, language.getRedundantConst(), FMPropertyManager.getFeatureForgroundColor(), REDUNDANT_TOOLTIP);
		add(labelIndetHidden);
	}

	private void createRowImplicitConst(int row) {
		createSymbol(row, IMPLICIT, false, IMPLICIT_TOOLTIP);
		final Label labelIndetHidden = createLabel(row, language.getImplicitConst(), FMPropertyManager.getFeatureForgroundColor(), IMPLICIT_TOOLTIP);
		add(labelIndetHidden);
	}

	private void createRowTautologyConst(int row) {
		createSymbol(row, FALSE_OPT, false, TAUTOLOGY_CONST_TOOLTIP);
		final Label labelIndetHidden = createLabel(row, language.getTautologyConst(), FMPropertyManager.getFeatureForgroundColor(), TAUTOLOGY_CONST_TOOLTIP);
		add(labelIndetHidden);
	}

	private void createRowIndetHidden(int row) {
		createSymbol(row, FALSE_OPT, true, INDET_HIDDEN_TOOLTIP);
		final Label labelIndetHidden = createLabel(row, language.getIndetHidden(), FMPropertyManager.getFeatureForgroundColor(), INDET_HIDDEN_TOOLTIP);
		add(labelIndetHidden);
	}

	private void createRowFalseOpt(int row) {
		createSymbol(row, FALSE_OPT, true, FALSE_OPT_TOOLTIP);
		final Label labelFalseOpt = createLabel(row, language.getFalseOptional(), FMPropertyManager.getFeatureForgroundColor(), FALSE_OPT_TOOLTIP);
		add(labelFalseOpt);

	}

	private void createRowTitle() {
		final Label labelTitle = new Label();
		labelTitle.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		labelTitle.setFont(DEFAULT_FONT);
		labelTitle.setText(language.getLagendTitle());
		labelTitle.setLabelAlignment(PositionConstants.LEFT);
		layout.setConstraint(labelTitle, new Rectangle(3, 0, width, ROW_HEIGHT));
		add(labelTitle);
	}

	private void createRowAlternative(int row) {
		createGroupTypeSymbol(row, ALTERNATIVE);
		final Label labelOr = createLabel(row, language.getAlternative(), FMPropertyManager.getFeatureForgroundColor(), ALTERNATIVE_TOOLTIP);

		add(labelOr);
	}

	private void createRowOr(int row) {
		createGroupTypeSymbol(row, OR);
		final Label labelOr = createLabel(row, language.getOr(), FMPropertyManager.getFeatureForgroundColor(), OR_TOOLTIP);
		add(labelOr);
	}

	private void createRowOptional(int row) {
		final PolylineConnection p = createConnectionTypeSymbol(row, false);
		add(p);
		final Label labelMandatory = createLabel(row, language.getOptional(), FMPropertyManager.getFeatureForgroundColor(), OPTIONAL_TOOLTIP);
		add(labelMandatory);
	}

	private void createRowMandatory(int row) {
		final PolylineConnection p = createConnectionTypeSymbol(row, true);
		add(p);
		final Label labelMandatory = createLabel(row, language.getMandatory(), FMPropertyManager.getFeatureForgroundColor(), MANDATORY_TOOLTIP);
		add(labelMandatory);
	}

	private void createRowAbstract(int row) {
		createSymbol(row, ABSTRACT, true, ABSTRACT_TOOLTIP);
		final Label labelAbstract = createLabel(row, language.getAbstract(), FMPropertyManager.getFeatureForgroundColor(), ABSTRACT_TOOLTIP);
		add(labelAbstract);
	}

	private void createRowImported(int row) {
		createSymbol(row, IMPORTED, true, IMPORTED_TOOLTIP);
		final Label labelImported = createLabel(row, language.getImported(), FMPropertyManager.getFeatureForgroundColor(), IMPORTED_TOOLTIP);
		add(labelImported);
	}

	private void createRowInherited(int row) {
		createSymbol(row, INHERITED, true, INHERITED_TOOLTIP);
		final Label labelInherited = createLabel(row, language.getInherited(), FMPropertyManager.getFeatureForgroundColor(), INHERITED_TOOLTIP);
		add(labelInherited);
	}

	private void createRowInterfaced(int row) {
		createSymbol(row, INTERFACED, true, INTERFACED_TOOLTIP);
		final Label labelInterfaced = createLabel(row, language.getInterfaced(), FMPropertyManager.getFeatureForgroundColor(), INTERFACED_TOOLTIP);
		add(labelInterfaced);
	}

	private void createRowConcrete(int row) {
		createSymbol(row, CONCRETE, true, CONCRETE_TOOLTIP);
		final Label labelConcrete = createLabel(row, language.getConcrete(), FMPropertyManager.getFeatureForgroundColor(), CONCRETE_TOOLTIP);
		add(labelConcrete);
	}

	private void createRowHidden(int row) {
		createSymbol(row, HIDDEN, true, HIDDEN_TOOLTIP);
		final Label labelHidden = createLabel(row, language.getHidden(), HIDDEN_FOREGROUND, HIDDEN_TOOLTIP);
		add(labelHidden);
	}

	private void createRowCollapsed(int row) {
		createCollapsedSymbol(row, COLLAPSED_TOOLTIP);
		final Label labelCollapsed = createLabel(row, language.getCollapsed(), FMPropertyManager.getFeatureForgroundColor(), COLLAPSED_TOOLTIP);
		add(labelCollapsed);
	}

	private void createRowDead(int row) {
		createSymbol(row, DEAD, true, DEAD_TOOLTIP);
		final Label labelDead = createLabel(row, language.getDead(), FMPropertyManager.getFeatureForgroundColor(), DEAD_TOOLTIP);
		add(labelDead);

	}

	private Label createLabel(int row, String text, Color foreground, String tooltip) {
		final Label label = new Label(text);
		label.setLabelAlignment(PositionConstants.LEFT);
		layout.setConstraint(label, new Rectangle(LABEL_PADDING, (ROW_HEIGHT * row) - LIFT, width - LABEL_PADDING, ROW_HEIGHT));
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
		final Figure toolTipContent = new Figure();
		toolTipContent.setLayoutManager(new GridLayout());
		toolTipContent.add(new Label(text));
		return toolTipContent;
	}

	/**
	 *
	 * @param row the row in which the group type symbol shall appear
	 * @param type AND, OR, ALTERNATIVE
	 */
	private void createGroupTypeSymbol(int row, int type) {
		boolean fill = true;
		boolean decoration = true;
		String toolTipText = "";
		if (type == AND) {
			fill = false;
		} else if (type == OR) {
			toolTipText = OR_TOOLTIP;
			fill = true;
			decoration = true;
		} else {
			toolTipText = ALTERNATIVE_TOOLTIP;
			fill = false;
			decoration = true;
		}
		// otherwise type must be ALTERNATIVE and decoration = false;

		final Point p1 = new Point(GROUPTYPE_PADDING + SYMBOL_SIZE, ((ROW_HEIGHT * row) + SYMBOL_SIZE) - LIFT);
		final Point p2 = new Point((GROUPTYPE_PADDING + (SYMBOL_SIZE / 2)), (ROW_HEIGHT * row) - LIFT);
		final Point p3 = new Point(GROUPTYPE_PADDING, ((ROW_HEIGHT * row) + SYMBOL_SIZE) - LIFT);

		final PolylineConnection line = new PolylineConnection();
		line.setForegroundColor(FMPropertyManager.getConnectionForegroundColor());

		line.setEndpoints(p2, p3);
		if (decoration) {
			final RotatableDecoration sourceDecoration = new LegendRelationDecoration(fill, p1);
			line.setSourceDecoration(sourceDecoration);
		}
		final PolylineConnection line2 = new PolylineConnection();
		line2.setForegroundColor(FMPropertyManager.getConnectionForegroundColor());

		line2.setEndpoints(p2, p1);
		this.add(line);
		this.add(line2);
		final Figure toolTipContent = createToolTipContent(toolTipText);
		line.setToolTip(toolTipContent);
		line2.setToolTip(toolTipContent);
		setForegroundColor(FMPropertyManager.getConnectionForegroundColor());

	}

	private PolylineConnection createConnectionTypeSymbol(int row, boolean mandatory) {

		final PolylineConnection p = new PolylineConnection();
		p.setForegroundColor(FMPropertyManager.getConnectionForegroundColor());
		final CircleDecoration circleDecoration = new CircleDecoration(mandatory);
		p.setSourceDecoration(circleDecoration);
		final Point source = new Point(MANDATORY_PADDING, ((ROW_HEIGHT * row) - LIFT) + (SYMBOL_SIZE / 2));
		final Point target = new Point(MANDATORY_PADDING + (SYMBOL_SIZE / 2), (row * ROW_HEIGHT) - LIFT);

		p.setEndpoints(source, target);
		p.setBounds(new Rectangle(getBounds()).shrink(-1, -1));
		String toolTipText;
		if (mandatory) {
			toolTipText = MANDATORY_TOOLTIP;
		} else {
			toolTipText = OPTIONAL_TOOLTIP;
		}
		p.setToolTip(createToolTipContent(toolTipText));
		return p;
	}

	private void createCollapsedSymbol(int row, String toolTip) {
		final CollapsedDecoration collapsedDecoration = new CollapsedDecoration();

		final int x1 = ((SYMBOL_SIZE / 2) - 2);
		final int y1 = ((ROW_HEIGHT * row) - (LIFT_2 / 2));
		final int x2 = SYMBOL_SIZE + (SYMBOL_SIZE / 2);
		final int y2 = (((ROW_HEIGHT * row) + SYMBOL_SIZE) - LIFT_2);
		final Point p1 = new Point(x1, y1);
		collapsedDecoration.isLegendEntry = true;
		collapsedDecoration.setSize(x2 - x1, y2 - y1);
		collapsedDecoration.setToolTip(createToolTipContent(toolTip));
		collapsedDecoration.setLocation(p1);
		this.add(collapsedDecoration);
	}

	private void createSymbol(int row, int type, boolean feature, String toolTip) {
		final int x1 = ((SYMBOL_SIZE / 2) - 2);
		final int y1 = ((ROW_HEIGHT * row) - (LIFT_2 / 2));
		final int x2 = SYMBOL_SIZE + (SYMBOL_SIZE / 2);
		final int y2 = (((ROW_HEIGHT * row) + SYMBOL_SIZE) - LIFT_2);
		final Point p1 = new Point(x1, y1);

		final Label label = new Label();
		final Figure rect = new RectangleFigure();
		switch (type) {
		case (DEAD):
			label.setIcon(FM_ERROR);
			break;
		case (FALSE_OPT):
			label.setIcon(FM_WARNING);
			break;
		case (REDUNDANT):
			label.setIcon(FM_INFO);
			break;
		case (VOID_MODEL):
			label.setIcon(FM_ERROR);
			break;
		case (ABSTRACT):
			rect.setBorder(FMPropertyManager.getAbsteactFeatureBorder(false));
			rect.setBackgroundColor(FMPropertyManager.getAbstractFeatureBackgroundColor());
			break;
		case (CONCRETE):
			rect.setBorder(FMPropertyManager.getConcreteFeatureBorder(false));
			rect.setBackgroundColor(FMPropertyManager.getConcreteFeatureBackgroundColor());
			break;
		case (HIDDEN):
			rect.setBorder(FMPropertyManager.getHiddenLegendBorder());
			break;
		case (IMPLICIT):
			rect.setBorder(IMPLICIT_CONSTRAINT_BORDER);
			rect.setBackgroundColor(FMPropertyManager.getWarningColor());
			break;
		case (IMPORTED):
			rect.setBorder(FMPropertyManager.getImportedFeatureBorder());
			break;
		case (INHERITED):
			rect.setBorder(FMPropertyManager.getInheritedFeatureBorder());
			break;
		case (INTERFACED):
			rect.setBorder(FMPropertyManager.getInterfacedFeatureBorder());
			break;
		case (EXPLANATION):
			rect.setBorder(FMPropertyManager.getInterfacedFeatureBorder());
			break;
		}
		rect.setSize(x2 - x1, y2 - y1);
		rect.setLocation(p1);
		rect.setToolTip(createToolTipContent(toolTip));

		if (label.getIcon() != null) {
			label.setBounds(rect.getBounds());
			add(label);
		} else {
			add(rect);
		}
	}

	public void recreateLegend() {
		removeAll();
		setLocation(graphicalFeatureModel.getLayout().getLegendPos());
		refreshProperties(graphicalFeatureModel.getFeatureModel());
		setLegendSize();
		createRows();
	}

	private void createExplanationEntry() {
		final Explanation<?> explanation = graphicalFeatureModel.getActiveExplanation();

		final XYLayout layout = new XYLayout();
		final Figure explanationFigure = new Figure();
		explanationFigure.setLayoutManager(layout);
		explanationFigure.setToolTip(createToolTipContent(EXPLANATION_TOOLTIP));

		final Point target = new Point(0, ((ROW_HEIGHT * row) - LIFT) + (SYMBOL_SIZE / 5));
		explanationFigure.setLocation(target);

		final int x_SymbolStart = SYMBOL_SIZE / 2;
		int y_Entry = explanationFigure.getLocation().y;

		// Label left
		final Label labelExplanation = new Label();
		labelExplanation.setText(language.getExplanation());
		explanationFigure.setToolTip(createToolTipContent(explanation.getWriter().getString()));
		final int widthInPixels = createLabel(1, labelExplanation.getText(), FMPropertyManager.getFeatureForgroundColor(), "").getPreferredSize().width + 25;

		// SetWidth depending of string
		explanationFigure.setSize(widthInPixels, 18 + (2 * ROW_HEIGHT) + 5);
		setSize(getSize().width < widthInPixels ? widthInPixels : getSize().width, getSize().height + explanationFigure.getSize().height);

		labelExplanation.setLabelAlignment(PositionConstants.LEFT);
		labelExplanation.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		labelExplanation.setBackgroundColor(FMPropertyManager.getDiagramBackgroundColor());
		labelExplanation.setFont(DEFAULT_FONT);
		labelExplanation.setSize(getSize().width, (2 * ROW_HEIGHT) + 2);

		labelExplanation.setLocation(new Point(x_SymbolStart, y_Entry));
		y_Entry += 2 * ROW_HEIGHT;

		// Add Red to dark red Gradient
		final TwoColorGradientLine redToBlack =
			new TwoColorGradientLine(new Color(null, 255, 0, 0), new Color(null, 0, 0, 0), labelExplanation.getPreferredSize().width, 6);
		redToBlack.setLocation(new Point(x_SymbolStart, y_Entry));
		y_Entry += redToBlack.getSize().height;

		// Label left
		final Label labelLeft = new Label(language.getLikelyCause());
		labelLeft.setLabelAlignment(PositionConstants.LEFT);
		labelLeft.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		labelLeft.setBackgroundColor(FMPropertyManager.getDiagramBackgroundColor());
		labelLeft.setFont(DEFAULT_FONT);
		labelLeft.setSize(labelLeft.getPreferredSize().width + 2, ROW_HEIGHT);
		labelLeft.setLocation(new Point(redToBlack.getLocation().x, y_Entry));

		// label right
		final Label labelRight = new Label(language.getUnlikelyCause());
		labelRight.setLabelAlignment(PositionConstants.RIGHT);
		labelRight.setForegroundColor(FMPropertyManager.getFeatureForgroundColor());
		labelRight.setBackgroundColor(FMPropertyManager.getDiagramBackgroundColor());
		labelRight.setFont(DEFAULT_FONT);
		labelRight.setSize(labelRight.getPreferredSize().width + 2, ROW_HEIGHT);
		labelRight.setLocation(new Point((redToBlack.getLocation().x + redToBlack.getSize().width) - labelRight.getPreferredSize().width, y_Entry));

		explanationFigure.add(labelExplanation);
		explanationFigure.add(redToBlack);
		explanationFigure.add(labelLeft);
		explanationFigure.add(labelRight);

		explanationFigure.setOpaque(true);
		this.add(explanationFigure);
	}
}
