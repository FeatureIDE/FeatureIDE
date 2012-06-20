package de.ovgu.featureide.core.typecheck.actions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.TypeChecker;
import de.ovgu.featureide.core.typecheck.TypecheckCorePlugin;
import de.ovgu.featureide.core.typecheck.check.FieldCheck;
import de.ovgu.featureide.core.typecheck.check.ICheckPlugin;
import de.ovgu.featureide.core.typecheck.check.MethodCheck;
import de.ovgu.featureide.core.typecheck.check.TypeCheck;
import de.ovgu.featureide.core.typecheck.correction.ConsoleProblemHandler;

/**
 * 
 * @author Sönke Holthusen
 * 
 */
public class TypecheckCleanAction implements IObjectActionDelegate {

    private IStructuredSelection selection;

    @Override
    public void run(IAction action) {
	Map<IFeatureProject, TypeChecker> typechecker = TypecheckCorePlugin
		.getDefault().typechecker;
	Object obj = selection.getFirstElement();
	if (obj instanceof IResource) {
	    IResource res = (IResource) obj;

	    IFeatureProject project = CorePlugin.getFeatureProject(res);

	    if (Arrays.asList(TypecheckCorePlugin.supportedComposers).contains(
		    project.getComposerID())) {
		List<ICheckPlugin> plugins = new ArrayList<ICheckPlugin>();
		    plugins.add(new MethodCheck());
		    plugins.add(new FieldCheck());
		    plugins.add(new TypeCheck());

		typechecker.put(project, new TypeChecker(plugins,
			new ConsoleProblemHandler()));
		typechecker.get(project).setParameters(
			project.getFeatureModel(), project.getSourcePath());
		typechecker.get(project).run();
	    } else {
		// TODO: change output method
		System.out.println("unsupported composer found");
	    }
	}
    }

    @Override
    public void selectionChanged(IAction action, ISelection selection) {
	this.selection = (IStructuredSelection) selection;
    }

    @Override
    public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	// TODO Auto-generated method stub

    }

}
