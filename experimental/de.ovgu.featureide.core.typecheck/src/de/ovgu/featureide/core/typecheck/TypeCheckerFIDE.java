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
package de.ovgu.featureide.core.typecheck;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.check.ICheckPlugin;
import de.ovgu.featureide.core.typecheck.check.OriginalCheck;
import de.ovgu.featureide.core.typecheck.check.TypeReferenceCheck;
import de.ovgu.featureide.core.typecheck.correction.FIDEProblemHandler;
import de.ovgu.featureide.core.typecheck.correction.IProblemHandler;

/**
 * TODO description
 * 
 * @author soenke
 */
public class TypeCheckerFIDE {
    public static Map<IFeatureProject, TypeChecker> typechecker = new HashMap<IFeatureProject, TypeChecker>();
    
    public static final String CHECK_MARKER = "typecheckmarker";

    public void run(IFeatureProject project) {
	run(project, false);
    }

    public  void run(final IFeatureProject project, final boolean clean) {
	Job job = new Job("Typechecking " + project.getProjectName()) {
	    
	    @Override
	    protected IStatus run(IProgressMonitor monitor) {
		TypeChecker tc = getTypeChecker(project, clean);
		tc.setParameters(project.getFeatureModel(), project.getSourcePath());
		tc.run();
		return Status.OK_STATUS;
	    }
	};
	
	job.setPriority(Job.LONG);
	job.schedule();
    }

    public  TypeChecker getTypeChecker(IFeatureProject project,
	    boolean clean) {
	List<ICheckPlugin> plugins = new ArrayList<ICheckPlugin>();
	plugins.add(new TypeReferenceCheck());
	plugins.add(new OriginalCheck());

	List<IProblemHandler> handlers = new ArrayList<IProblemHandler>();
	handlers.add(new FIDEProblemHandler(project));
	//handlers.add(new ConsoleProblemHandler());

	return getTypeChecker(project, plugins, handlers, clean);
    }

    private  TypeChecker getTypeChecker(IFeatureProject project,
	    List<ICheckPlugin> plugins, List<IProblemHandler> handlers,
	    boolean clean) {
	if (clean || !typechecker.containsKey(project)) {
	    System.out.println("no tc for the project or clean is false: " + clean);
	    typechecker.put(project, new TypeChecker(plugins, handlers));
	}
	return typechecker.get(project);
    }
}
