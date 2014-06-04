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
package de.ovgu.featureide.ahead.actions;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.ahead.AheadComposer;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;

/**
 * Test if a composer conversion is possible for the selected project.
 * 
 * @author Jens Meinicke
 */
public class ComposerPropertyTester extends PropertyTester {

    private static IFeatureProject FEATURE_PROJECT;
    private static String FH_COMPOSER_ID = "de.ovgu.featureide.composer.featurehouse";

	@Override
    public boolean test(Object receiver, String property, Object[] args,
            Object expectedValue) {
    	if (!(receiver instanceof IProject)) {
    		return false;
    	}
    	IProject project = (IProject) receiver;
    	FEATURE_PROJECT = CorePlugin.getFeatureProject(project);
    	if (FEATURE_PROJECT == null || !project.isOpen()) {
    		return false;
    	}
    	String composerID = FEATURE_PROJECT.getComposerID();
		if (composerID != null) {
	    	if (expectedValue.equals("FeatureHouse")) {
		    	if (AheadComposer.COMPOSER_ID.equals(composerID)) {
		    		return true;// TODO #454 COMPOSER CONVERSION: currently conversion is unavailable because
		    					 // 	 it seems not to be perfect and could lead to problems. 
		    	}
		    } else if (FH_COMPOSER_ID.equals(composerID)) {
		    		return true;
		    }
    	}
    	return false;
    }

	
	public static IFeatureProject getFeatureProject() {
		return FEATURE_PROJECT;
	}
	
	public static String getFHComposerID() {
		return FH_COMPOSER_ID;
	}
}