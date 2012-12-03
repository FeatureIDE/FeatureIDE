package de.ovgu.featureide.featurehouse.meta;
import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;

/**
 * Test if a composer conversion is possible for the selected project.
 * 
 * @author Jens Meinicke
 */
public class ComposerPropertyTester extends PropertyTester {

    private static IFeatureProject FEATURE_PROJECT;
    
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
	    	if (FEATURE_PROJECT.getComposerID().equals(FeatureHouseComposer.COMPOSER_ID)) {
	    		return true; 
	    	}
    	}
    	return false;
    }

	
	public static IFeatureProject getFeatureProject() {
		return FEATURE_PROJECT;
	}

}