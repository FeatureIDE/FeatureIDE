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
package de.ovgu.featureide.core.typecheck.correction;

import java.util.Collection;

import de.ovgu.featureide.core.typecheck.check.CheckProblem;

/**
 * TODO description
 * 
 * @author Soenke Holthusen
 */
public class ConsoleProblemHandler implements IProblemHandler {
    /*
     * (non-Javadoc)
     * 
     * @see
     * de.ovgu.featureide.core.typecheck.correction.IProblemHandler#handleProblems
     * (java.util.Collection)
     */
    @Override
    public void handleProblems(Collection<CheckProblem> problems) {
	for (CheckProblem problem : problems) {
	    System.out.println(problem);
	    System.out.println("Action which could fix the problem: ");
	    for(Action action : problem.getActions()){
		System.out.println(action);
	    }
	}
	System.out.println("Reported " + problems.size() + " Problems");
    }

    /* (non-Javadoc)
     * @see de.ovgu.featureide.core.typecheck.correction.IProblemHandler#log(java.lang.String)
     */
    @Override
    public void log(String message) {
	System.out.println(message);
    }
}
