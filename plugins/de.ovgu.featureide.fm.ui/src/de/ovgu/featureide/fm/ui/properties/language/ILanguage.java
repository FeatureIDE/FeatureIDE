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
package de.ovgu.featureide.fm.ui.properties.language;

/**
 * Interface of the extension point 
 * <code>"de.ovgu.featureide.fm.core.language"</code> 
 * 
 * @author Jens Meinicke
 */
public interface ILanguage {
	
	
	/**
	 * @return The translation for: "Redundant constraint"
	 */	
	public String getRedundantConst();
	
	/**
	 * @return The translation for: "False optional constraint"
	 */	
	public String getFalseOptionalConst();
	
	/**
	 * @return The translation for: "Dead constraint"
	 */	
	public String getDeadConst();
	 
	/**
 	 * @return The translation for: "Unsatisfiable constraint"
	 */	
	public String getUnsatisfiableConst();
	 
	/**
	 * @return The translation for: "Constraint is tautology"
	 */	
	public String getTautologyConst();
	 
	/**
	 * @return The translation for: "Constraint makes the model void"
	 */	
	public String getVoidModelConst();
	 
	 
	/**
	 * @return The translation for: "Indeterminate hidden"
	 */	
	public String getIndetHidden();
	
	/**
	 * @return The title of the legend
	 */
	public String getLagendTitle();
	
	/**
	 * @return The name of the language
	 */
	public String getName();
	
	/**
	 * @return The word for: "mandatory"
	 */
	public String getMandatory();
	
	/**
	 * @return The word for: "abstract"
	 */
	public String getAbstract();
	
	/**
	 * @return The word for: "concrete"
	 */
	public String getConcrete();
	
	/**
	 * @return The word for: "Hidden"
	 */
	public String getHidden();
	
	/**
	 * @return The translation for: "Dead"
	 */
	public String getDead();
	
	/**
	 * @return The translation for: "False Optional"
	 */
	public String getFalseOptional();
	
	/**
	 * @return The word for: "alternative"
	 */
	public String getAlternative();
	
	/**
	 * @return The word for: "or"
	 */
	public String getOr();
	
	/**
	 * @return The word for: "optional"
	 */
	public String getOptional();
}
