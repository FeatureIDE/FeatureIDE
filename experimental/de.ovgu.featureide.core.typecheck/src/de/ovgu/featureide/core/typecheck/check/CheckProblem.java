/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.typecheck.check;

import java.util.List;
import java.util.Set;

import AST.TypeDecl;
import de.ovgu.featureide.core.typecheck.correction.Action;
import de.ovgu.featureide.fm.core.Feature;

/**
 * Provides information about a problem, encountered by the typechecks
 * 
 * @author Soenke Holthusen
 */
public class CheckProblem {
    private Feature feature;
    private TypeDecl classs;
    private String filename;
    private int linenumber;
    private String message;
    private Set<Feature> providingFeatures;
    private ICheckPlugin origin;
    
    private int severity = SEVERITY_INFO;

    /**
     * @return the severity
     */
    public int getSeverity() {
        return severity;
    }

    /**
     * @param severity the severity to set
     */
    public void setSeverity(int severity) {
        this.severity = severity;
    }

    private List<Action> actions;

    /**
     * @return the origin
     */
    public ICheckPlugin getOrigin() {
	return origin;
    }

    /**
     * @param origin
     *            the origin to set
     */
    public void setOrigin(ICheckPlugin origin) {
	this.origin = origin;
    }

    public CheckProblem(Feature feature, TypeDecl cd, String filename,
	    int linenumber, String message, Set<Feature> providing_features) {
	this.feature = feature;
	this.classs = cd;
	this.filename = filename;
	this.linenumber = linenumber;
	this.message = message;
	this.providingFeatures = providing_features;
    }

    public String toString() {
	StringBuilder builder = new StringBuilder();
	builder.append(message).append(" in Feature ")
		.append(feature.getName());
	if (classs != null) {
	    builder.append(" in Class ").append(classs.name());
	}
	builder.append(" at line ").append(linenumber);
	if (providingFeatures != null && !providingFeatures.isEmpty()) {
	    builder.append("\nFollowing features could solve dependencies: ");
	    int i = 0;
	    for (Feature f : providingFeatures) {
		builder.append(f);
		if (i++ < providingFeatures.size() - 1) {
		    builder.append(", ");
		}
	    }
	}
	return builder.toString();
    }

    /**
     * @return the feature
     */
    public Feature getFeature() {
	return feature;
    }

    /**
     * @return the filename
     */
    public String getFilename() {
	return filename;
    }

    /**
     * @return the line number
     */
    public int getLinenumber() {
	return linenumber;
    }

    /**
     * @return the message
     */
    public String getMessage() {
	return message;
    }

    /**
     * @return the providingFeatures
     */
    public Set<Feature> getProvidingFeatures() {
	return providingFeatures;
    }

    public void setActions(List<Action> actions) {
	this.actions = actions;
    }

    public List<Action> getActions() {
	return this.actions;
    }
    
    public static final int SEVERITY_INFO = 0;
    public static final int SEVERITY_WARNING = 1;
    public static final int SEVERITY_ERROR = 2;
}
