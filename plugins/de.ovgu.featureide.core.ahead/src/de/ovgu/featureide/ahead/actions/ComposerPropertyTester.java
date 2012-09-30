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
    	if (FEATURE_PROJECT.getComposerID() != null) {
	    	if (expectedValue.equals("FeatureHouse")) {
		    	if (FEATURE_PROJECT.getComposerID().equals(AheadComposer.COMPOSER_ID)) {
		    		return false;// TODO #454 COMPOSER CONVERSION: currently conversion is unavailable because
		    					 // 	 it seems not to be perfect and could lead to problems. 
		    	}
		    } else if (FEATURE_PROJECT.getComposerID().equals(FH_COMPOSER_ID)) {
		    		return false;
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