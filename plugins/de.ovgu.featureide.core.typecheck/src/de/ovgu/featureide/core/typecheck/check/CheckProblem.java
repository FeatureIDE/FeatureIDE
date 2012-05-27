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
package de.ovgu.featureide.core.typecheck.check;

import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author soenke
 */
public class CheckProblem {
    private Feature feature;
    private String filename;
    private int linenumber;
    private String message;

    public CheckProblem(Feature feature, String filename, int linenumber,
	    String message) {
	this.feature = feature;
	this.filename = filename;
	this.linenumber = linenumber;
	this.message = message;
    }

    public String toString() {
	StringBuilder builder = new StringBuilder();
	builder.append("Problem: ").append(message).append(" in Feature ")
		.append(feature.getName()).append(" in File ").append(filename)
		.append(" at line ").append(linenumber);
	return builder.toString();
    }
}
