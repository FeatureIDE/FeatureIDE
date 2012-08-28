/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.ui.views.featurestatistics;

	import java.util.ArrayList;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
	import org.eclipse.core.runtime.IStatus;
	import org.eclipse.core.runtime.Status;
	import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.IStructuredContentProvider;
	import org.eclipse.jface.viewers.ITreeContentProvider;
	import org.eclipse.jface.viewers.Viewer;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.views.featuremodeleditview.TreeParent;
import de.ovgu.featureide.ui.views.FeatureStatistics;

// TODO differences should be highlighted
public class StatisticsContentProvider implements IStructuredContentProvider,
		ITreeContentProvider, GUIDefaults {


	private IProject project;	
	protected static final int INDEX_STATISTICS_BEFORE = 5;
	protected static final int INDEX_STATISTICS_AFTER = 6;
	
	private static final long TIMEOUT_CONFIGURATION = 10000;
	
	private final FeatureStatistics view;
	private IFeatureProject featureProject;
	public static ArrayList<String> viewableContent = new ArrayList<String>();
	public  String[] compactList = new String[0];

	TreeParent invisibleRoot = new TreeParent("");

	public StatisticsContentProvider(FeatureStatistics featureStatistics) {
		this.view = featureStatistics;
	}

	/**
	 * @param featureStatistics
	 */
	
	public void inputChanged(Viewer v, Object oldInput, Object newInput) {
	}

	public void dispose() {
		invisibleRoot = null;
	}	

	public Object getParent(Object child) {
		if (child instanceof TreeElement)
			return ((TreeElement) child).getParent();
		return null;
	}

	public Object[] getChildren(Object parent) {
		if (parent instanceof TreeElement)
			return ((TreeElement) parent).getChildren();
		return new Object[0];
	}

	public boolean hasChildren(Object parent) {
		if (parent instanceof TreeElement)
			return ((TreeElement) parent).hasChildren();
		return false;
	}

	/**
	 * Displays a default message if the automatic calculations are disabled and
	 * there are no statistics displayed.
	 */
	public void defaultManualContent() {
		if (invisibleRoot.getChildren().length <= 1) {
		refresh();
		}
	}
	
	public void defaultContent() {
		if (invisibleRoot != null) {
		refresh();
		}
	}

	private boolean cancel = false;
	protected void refresh() {
		UIJob job_setColor = new UIJob("Refresh edit view") {
			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				if (!view.getViewer().getControl().isDisposed()) {
					view.getViewer().refresh();
				}
				return Status.OK_STATUS;
			}
		};
		job_setColor.setPriority(Job.INTERACTIVE);
		job_setColor.schedule();
	}

	/**
	 * Stops the calculation and the running job
	 * @param value
	 */
	public void setCanceled(boolean value) {
		cancel  = value;
	}
	
	/**
	 * @return <code>true</code> if the calculation is canceled
	 */
	public boolean isCanceled() {
		return cancel;
	}
	
	public Object[] getElements(Object parent) {		
		if(compactList.length == 0){
			return new String[]{};
		} return compactList;
	}
	
		
	
	
public ArrayList<String> getFeatureModelSpecification(final FeatureModelEditor editor) {
		
		FeatureModel model = editor.getFeatureModel();		
		project = editor.getGrammarFile().getResource().getProject();
		featureProject = CorePlugin.getFeatureProject(project);
				
		
		viewableContent.add("Project: " + project.getName());
		
		final int features = model.getNumberOfFeatures();
		viewableContent.add("Features:");

		final int concrete = model.getAnalyser().countConcreteFeatures();

		viewableContent.add(" Conrete Features: "
				+ new Integer(concrete).toString());

		viewableContent.add(" Abstract Features: "
				+ new Integer(features - concrete).toString());

		final int terminal = model.getAnalyser().countTerminalFeatures();
		viewableContent.add(" Primitive Features: "
				+ new Integer(terminal).toString());

		viewableContent.add(" Compound Features: "
				+ new Integer(features - terminal).toString());

		final int hidden = model.getAnalyser().countHiddenFeatures();

		viewableContent.add(" Hidden Features: "
				+ new Integer(hidden).toString());
		viewableContent.add("Total: " + new Integer(features).toString());
		viewableContent.add("\n");

		viewableContent.add("Configurations: "
				+ calculateNumberOfVariants2(model, true));

		viewableContent.add("Program Variants: "
				+ calculateNumberOfVariants2(model, false));
		
				
		viewableContent.add("Composer: " + ComposerExtensionManager.getInstance()
				.getComposerById(featureProject.getComposerID()).getName());
		
		return viewableContent;

	}


	private String calculateNumberOfVariants2(FeatureModel model,
			boolean ignoreAbstractFeatures) {

		String variants = ignoreAbstractFeatures ? "configurations"
				: "program variants";
		TreeParent p = new TreeParent("Number of " + variants, null, true) {
			@Override
			public void initChildren() {
			}
		};

		if (!ignoreAbstractFeatures
				&& model.getAnalyser().countConcreteFeatures() == 0) {
			// case: there is no concrete feature so there is only one program
			// variant,
			// without this the calculation least much to long
			p.addChild("1 " + variants);
			return "1";
		}
		final long number = new Configuration(model, false,
				ignoreAbstractFeatures).number(TIMEOUT_CONFIGURATION);
		String s = "";
		if (number < 0)
			s += "more than " + (-1 - number);
		else
			s += number;

		return s;
	}
	
	public void printSpec(ArrayList<String> arrList) {
		compactList = arrList.toArray(new String[arrList.size()]);
		viewableContent.clear();
		refresh();
	}
		
	/**
	 * @return <code>true</code> if the calculation is canceled
	 */
	

	

}
