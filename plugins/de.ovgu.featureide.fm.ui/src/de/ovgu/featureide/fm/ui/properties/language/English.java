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
package de.ovgu.featureide.fm.ui.properties.language;

import static de.ovgu.featureide.fm.core.localization.StringTable.ALTERNATIVE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_TAUTOLOGY;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_MODELIS_VOID;
import static de.ovgu.featureide.fm.core.localization.StringTable.ENGLISH;
import static de.ovgu.featureide.fm.core.localization.StringTable.FALSE_OPTIONAL_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.FROM_INTERFACE;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORTED;
import static de.ovgu.featureide.fm.core.localization.StringTable.INDETERMINATE_HIDDEN;
import static de.ovgu.featureide.fm.core.localization.StringTable.INHERITED;
import static de.ovgu.featureide.fm.core.localization.StringTable.OR;
import static de.ovgu.featureide.fm.core.localization.StringTable.REDUNDANT_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.UNSATISFIABLE_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.VOID_FEATURE_MODEL;

/**
 * Class implementing the extension point <code>"de.ovgu.featureide.fm.core.language"</code>
 *
 * @author Jens Meinicke
 * @author Florian Proksch
 * @author Stefan Krueger
 */
public class English implements ILanguage {

	public static final String NAME = ENGLISH;

	private static final String LEGEND = "Legend:";
	private static final String MANDATORY = "Mandatory";
	private static final String ABSTRACT = "Abstract";
	private static final String INTERFACED = FROM_INTERFACE;
	private static final String CONCRETE = "Concrete";
	private static final String HIDDEN = "Hidden";
	private static final String COLLAPSED = "Collapsed";
	private static final String DEAD = "Dead feature";
	private static final String FALSE_OPTIONAL = FALSE_OPTIONAL_FEATURE;
	private static final String OPTIONAL = "Optional";
	private static final String INDETHIDDEN = INDETERMINATE_HIDDEN;
	private static final String REDUNDANT = REDUNDANT_CONSTRAINT;
	private static final String IMPLICIT = "Implicit constraint";
	private static final String UNSATISFIABLE_CONST = UNSATISFIABLE_CONSTRAINT;
	private static final String TAUTOLOGY_CONST = CONSTRAINT_IS_TAUTOLOGY;
	private static final String VOID_MODEL_CONST = FEATURE_MODELIS_VOID;

	@Override
	public String getRedundantConst() {
		return REDUNDANT;
	}

	@Override
	public String getImplicitConst() {
		return IMPLICIT;
	}

	@Override
	public String getUnsatisfiableConst() {
		return UNSATISFIABLE_CONST;
	}

	@Override
	public String getTautologyConst() {
		return TAUTOLOGY_CONST;
	}

	@Override
	public String getVoidModelConst() {
		return VOID_MODEL_CONST;
	}

	@Override
	public String getVoidModel() {
		return VOID_FEATURE_MODEL;
	}

	@Override
	public String getIndetHidden() {
		return INDETHIDDEN;
	}

	@Override
	public String getName() {
		return NAME;
	}

	@Override
	public String getLagendTitle() {
		return LEGEND;
	}

	@Override
	public String getMandatory() {
		return MANDATORY;
	}

	@Override
	public String getAbstract() {
		return ABSTRACT;
	}

	@Override
	public String getImported() {
		return IMPORTED;
	}

	@Override
	public String getInherited() {
		return INHERITED;
	}

	@Override
	public String getInterfaced() {
		return INTERFACED;
	}

	@Override
	public String getConcrete() {
		return CONCRETE;
	}

	@Override
	public String getHidden() {
		return HIDDEN;
	}

	@Override
	public String getCollapsed() {
		return COLLAPSED;
	}

	@Override
	public String getDead() {
		return DEAD;
	}

	@Override
	public String getFalseOptional() {
		return FALSE_OPTIONAL;
	}

	@Override
	public String getAlternative() {
		return ALTERNATIVE;
	}

	@Override
	public String getOr() {
		return OR;
	}

	@Override
	public String getOptional() {
		return OPTIONAL;
	}

	@Override
	public String getExplanation() {
		return "The selected element is defect" + System.lineSeparator() + "because of the highlighted dependencies:";
	}

	@Override
	public String getLikelyCause() {
		return "likely cause";
	}

	@Override
	public String getUnlikelyCause() {
		return "unlikely cause";
	}

}
