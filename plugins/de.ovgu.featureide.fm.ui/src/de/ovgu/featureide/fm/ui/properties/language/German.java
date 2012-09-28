/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.ui.properties.language;


/**
 * Class implementing the extension point 
 * <code>"de.ovgu.featureide.fm.core.language"</code> 
 * 
 * @author Jens Meinicke
 * @author Florian Proksch
 * @author Stefan Krueger
 */
public class German implements ILanguage {

	public static final String name = "German";
	
	private static final String LEGEND = "Legende:";
	private static final String MANDATORY = "Obligatorisch";
	private static final String ABSTRACT = "Abstrakt";
	private static final String CONCRETE = "Konkret";
	private static final String HIDDEN = "Versteckt";
	private static final String DEAD = "Unwählbar";
	private static final String FALSE_OPTIONAL ="falsch-optional";
	private static final String ALTERNATIVE = "Alternative";
	private static final String OR = "Oder";
	private static final String OPTIONAL = "Optional";
	private static final String INDETHIDDEN = "versteckt & unbestimmbar";
	private static final String REDUNDANT = "Redundant";
	private static final String DEAD_CONST = "???";
	private static final String UNSATISFIABLE_CONST = "Unerfüllbar";
	private static final String TAUTOLOGY_CONST = "Tautologie";
	private static final String VOID_MODEL_CONST = "???";	
	
	
	@Override
	public String getRedundantConst() {
		return REDUNDANT;
	}
	
	@Override
	public String getDeadConst() {
		return DEAD_CONST;
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
	public String getIndetHidden() {
		return INDETHIDDEN;
	}
	
	@Override
	public String getName() {
		return name;
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
	public String getConcrete() {
		return CONCRETE;
	}

	@Override
	public String getHidden() {
		return HIDDEN;
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
}
