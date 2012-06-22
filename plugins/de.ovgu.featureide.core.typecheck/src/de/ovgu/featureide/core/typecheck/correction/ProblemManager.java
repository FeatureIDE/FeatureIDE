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
package de.ovgu.featureide.core.typecheck.correction;

import java.util.Collection;
import java.util.List;

import de.ovgu.featureide.core.typecheck.check.CheckProblem;

/**
 * TODO description
 * 
 * @author Soenke Holthusen
 */
public class ProblemManager {
    private Collection<CheckProblem> problems;
    private List<IProblemHandler> problem_handler;

    /**
     * 
     */
    public ProblemManager(List<IProblemHandler> problem_handler) {
	this.problem_handler = problem_handler;
    }
    
    public void addProblems(Collection<CheckProblem> problems){
	this.problems = problems;
    }
    
    public void run(){
	determineActions();
	for(IProblemHandler handler : problem_handler){
	    handler.handleProblems(problems);
	}
    }
    
    public void log(String message){
	for(IProblemHandler handler : problem_handler){
	    handler.log(message);
	}
    }
    
    private void determineActions(){
	for(CheckProblem problem : problems){
	    problem.setActions(problem.getOrigin().determineActions(problem));
	    problem.getOrigin();
	}
    }
}
