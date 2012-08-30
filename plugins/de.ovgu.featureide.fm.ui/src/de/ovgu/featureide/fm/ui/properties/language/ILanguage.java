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
 * Interface of the extension point 
 * <code>"de.ovgu.featureide.fm.core.language"</code> 
 * 
 * @author Jens Meinicke
 */
public interface ILanguage {
	
	
	/**
	 * @return The word for: "indeterminate hidden"
	 */	public String getRedundantConst();
	
	/**
	 * @return The word for: "indeterminate hidden"
	 */	public String getDeadConst();
	 
	/**
 	 * @return The word for: "indeterminate hidden"
	 */	public String getUnsatisfiableConst();
	 
	/**
	 * @return The word for: "indeterminate hidden"
	 */	public String getTautologyConst();
	 
	/**
	 * @return The word for: "indeterminate hidden"
	 */	public String getVoidModelConst();
	 
	 
	/**
	 * @return The word for: "indeterminate hidden"
	 */	public String getIndetHidden();
	
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
