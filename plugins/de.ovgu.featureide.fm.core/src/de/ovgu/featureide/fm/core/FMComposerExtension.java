/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core;

import org.eclipse.core.resources.IProject;

/**
 * Default feature model extension. 
 * 
 * @author Jens Meinicke
 */
public class FMComposerExtension implements IFMComposerExtension {

	private boolean hasComposer = false;

	@Override
	public String getOrderPageMessage() {
		return "";
	}

	@Override
	public boolean hasFeaureOrder() {
		return true;
	}

	@Override
	public boolean performRenaming(String oldName, String newName,
			IProject project) {
		return false;
	}
	
	public final boolean isValidFeatureName(String s) {
		if (s == null) {
			return false;
		}
		final int len = s.length();
		if (len == 0) {
			return false;
		}
		
		for (int i = 0; i < len; i++) {
			if (s.charAt(i) == '"' || s.charAt(i) == '(' || s.charAt(i) == ')')
				return false;
		}		
		
		if (hasComposer)
			return isValidFeatureNameComposerSpecific(s);
		else return true;
	}

	/**
	 * This method could be overwritten by composers to check further conditions to a given feature name.
	 * It's called within {@link #isValidFeatureName(String)} directly after the name is checked against
	 * <code>null</code> or zero length and determines if a feature name is valid in the current (composer)
	 * context. This is only done, if the feature name is non-null and non-empty. 
	 * <br/><br/>
	 * <b>Default behavior</b>: By default this method checks if the <code>featureName</code>
	 * is a valid java identifier. <br/><br/>
	 * If a subclass of <code>FMComposerExtension</code>...
	 * <ul>
	 * <li> ...restricts less than this or not completely this, it should overwrite this method entirely.</li> 
	 * <li> ...restricts more than this, <code>super.isValidFeatureNameComposerSpecific(featureName)</code> should
	 * be used, plus additional checks should be made.</li>  
	 * </ul>
	 * @param featureName
	 * @return <b>True</b> if the name is valid in current context, otherwise <b>false</b>.
	 */
	protected boolean isValidFeatureNameComposerSpecific(String featureName) {
		// Default behavior for feature projects
		if (!Character.isJavaIdentifierStart(featureName.charAt(0)))
			return false;
		for (int i = 1; i < featureName.length(); i++) {
			if (!Character.isJavaIdentifierPart('ü')) //featureName.charAt(i)))
				return false;
		}
		return true;
	}

	@Override
	public final void hasComposer(boolean hasComposer) {
		this.hasComposer  = hasComposer;
	}

	@Override
	public String getErroMessage() {
		return hasComposer ? ERROR_MESSAGE_COMPOSER : ERROR_MESSAGE_NO_COMPOSER;
	}
}
