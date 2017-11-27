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

import static de.ovgu.featureide.fm.core.localization.StringTable.ABSTRAKT;
import static de.ovgu.featureide.fm.core.localization.StringTable.ALTERNATIVE;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IST_TAUTOLOGIE;
import static de.ovgu.featureide.fm.core.localization.StringTable.EINGEKLAPPT;
import static de.ovgu.featureide.fm.core.localization.StringTable.FALSCH_OPTIONALES_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.GEERBT;
import static de.ovgu.featureide.fm.core.localization.StringTable.GERMAN;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPORTIERT;
import static de.ovgu.featureide.fm.core.localization.StringTable.KONKRET;
import static de.ovgu.featureide.fm.core.localization.StringTable.OBLIGATORISCH;
import static de.ovgu.featureide.fm.core.localization.StringTable.ODER;
import static de.ovgu.featureide.fm.core.localization.StringTable.REDUNDANTES_CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.UNBESTIMMBAR_VERSTECKTES_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.VERSTECKT;
import static de.ovgu.featureide.fm.core.localization.StringTable.VON_INTERFACE;

/**
 * Class implementing the extension point <code>"de.ovgu.featureide.fm.core.language"</code>
 *
 * @author Jens Meinicke
 * @author Florian Proksch
 * @author Stefan Krueger
 */
public class German implements ILanguage {

	public static final String NAME = GERMAN;

	private static final String LEGEND = "Legende:";
	private static final String MANDATORY = OBLIGATORISCH;
	private static final String ABSTRACT = ABSTRAKT;
	private static final String IMPORTED = IMPORTIERT;
	private static final String INHERITED = GEERBT;
	private static final String INTERFACED = VON_INTERFACE;
	private static final String CONCRETE = KONKRET;
	private static final String HIDDEN = VERSTECKT;
	private static final String COLLAPSED = EINGEKLAPPT;
	private static final String DEAD = "Unwählbar";
	private static final String FALSE_OPTIONAL = FALSCH_OPTIONALES_FEATURE;
	private static final String OR = ODER;
	private static final String OPTIONAL = "Optional";
	private static final String INDETHIDDEN = UNBESTIMMBAR_VERSTECKTES_FEATURE;
	private static final String REDUNDANT = REDUNDANTES_CONSTRAINT;
	private static final String IMPLICIT = "Implizites Constraint";
	private static final String UNSATISFIABLE_CONST = "Unerfüllbares Constraint";
	private static final String TAUTOLOGY_CONST = CONSTRAINT_IST_TAUTOLOGIE;
	private static final String VOID_MODEL_CONST = "Constraint macht Produktlinie unerfüllbar";
	private static final String VOID_MODEL = "Unerfüllbare Produktlinie";

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
		return VOID_MODEL;
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
		return "Das ausgewählte Element ist defekt" + System.lineSeparator() + "wegen der hervorgehobenen Abhängigkeiten:";
	}

	@Override
	public String getLikelyCause() {
		return "wahrsch. Ursache";
	}

	@Override
	public String getUnlikelyCause() {
		return "unwahrsch. Ursache";
	}
}
