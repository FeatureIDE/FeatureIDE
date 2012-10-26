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
package de.ovgu.featureide.fm.ui.views.featuremodeleditview;

import java.util.ConcurrentModificationException;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.progress.UIJob;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.views.FeatureModelEditView;

/**
 * Calculates the edit category and provides as a content to the view.
 * 
 * @author Thomas Thuem
 */
// TODO differences should be highlighted
public class ViewContentProvider implements IStructuredContentProvider,
		ITreeContentProvider, GUIDefaults {

	private static final String DEFAULT_MESSAGE = "Open a feature model.";
	private static final String DEFAULT_MANUAL_MESSAGE = "Start manual or activate automatic calculation to show statistics.";
	private static final String CALCULATING_MESSAGE = "Calculating...";
	
	private static final String HEAD_REFACTORING = "Refactoring: SPL unchanged";
	private static final String HEAD_GENERALIZATION = "Generalization: Products added";
	private static final String HEAD_SPECIALIZATION = "Specialization: Products removed";
	private static final String HEAD_ARBITRARY = "Arbitrary edit: Products added and removed";
	private static final String HEAD_OUTOFMEMORY = "Out of memory error!";
	private static final String HEAD_TIME_OUT = "SAT4J time out!";
	private static final String HEAD_ERROR = "An error has occured!";

	protected static final String NUMBER_FEATURES = "Number of features: ";
	protected static final String NUMBER_CONCRETE = "Number of concrete features: ";
	protected static final String NUMBER_ABSTRACT = "Number of abstract features: ";
	protected static final String NUMBER_PRIMITIVE = "Number of primitive features: ";
	protected static final String NUMBER_COMPOUND = "Number of compound features: ";
	protected static final String NUMBER_HIDDEN = "Number of hidden features: ";
	protected static final String NUMBER_CONSTRAINTS = "Number of constraints: ";
	protected static final String MODEL_VOID = "Feature model is valid (not void): ";
	protected static final String MODEL_TIMEOUT = MODEL_VOID + "timeout";
	
	private static final String STATISTICS_BEFORE = "Statistics on before edit version";
	private static final String STATISTICS_AFTER = "Statistics on after edit version";	
	
	/**
	 * time in seconds after the calculation is aborted by the SAT solver
	 */
	private static final int TIMEOUT = 20000;
	private static final long TIMEOUT_CONFIGURATION = 10000;

	private static final int INDEX_HEAD = 0;
	private static final int INDEX_ADDED = 2;
	private static final int INDEX_REMOVED = 3;
	protected static final int INDEX_STATISTICS_BEFORE = 5;
	protected static final int INDEX_STATISTICS_AFTER = 6;
	
	private static final int INDEX_VALID = 0;
	private static final int INDEX_FEATURES = 1;
	private static final int INDEX_CONCRETE = 2;
	private static final int INDEX_ABSTRACT = 3;
	private static final int INDEX_PRIMITIVE = 4;
	private static final int INDEX_COMPOUND = 5;
	private static final int INDEX_HIDDEN = 6;
	private static final int INDEX_CONSTRAINTS = 7;
	private static final int INDEX_CONFIGS = 8;
	private static final int INDEX_VARIANTS = 9;
	/**
	 * minimal number of available processors needed to activate parallelization
	 */
	private static final int PROCESSOR_LIMIT = 4;
	
	private final FeatureModelEditView view;

	TreeParent invisibleRoot = new TreeParent("");

	public ViewContentProvider(FeatureModelEditView view) {
		this.view = view;
	}

	public void inputChanged(Viewer v, Object oldInput, Object newInput) {
	}

	public void dispose() {
		invisibleRoot = null;
	}

	public Object[] getElements(Object parent) {
		if (parent.equals(view.getViewSite()))
			return getChildren(invisibleRoot);
		return getChildren(parent);
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
			invisibleRoot.setChild(new TreeObject(DEFAULT_MANUAL_MESSAGE, DEFAULT_IMAGE));
			refresh();
		}
	}
	
	public void defaultContent() {
		if (invisibleRoot != null) {
			invisibleRoot.setChild(new TreeObject(DEFAULT_MESSAGE, DEFAULT_IMAGE));
			refresh();
		}
	}

	private boolean cancel = false;

	private static ModelComparator comparator = new ModelComparator(TIMEOUT);
	
	public void calculateContent(final FeatureModel oldModel, final FeatureModel newModel, IProgressMonitor monitor) {
		if (oldModel.getRoot() == null || newModel.getRoot() == null)
			return;

		if (isCanceled()) return;
				
		if (invisibleRoot.getChildren().length <= 1) {
			//case: init
			// 		initializes the tree with default values
			if (invisibleRoot.getChildren().length < 1) {
				invisibleRoot.addChild(new TreeObject(CALCULATING_MESSAGE, DEFAULT_IMAGE));
			}
			invisibleRoot.addChild("");
			invisibleRoot.addChild(new TreeObject(CALCULATING_MESSAGE, DEFAULT_IMAGE));
			invisibleRoot.addChild(new TreeObject(CALCULATING_MESSAGE, DEFAULT_IMAGE));
			invisibleRoot.addChild("");
			
			addStatistics(invisibleRoot, STATISTICS_BEFORE, oldModel, INDEX_STATISTICS_BEFORE, true, null);
			addStatistics(invisibleRoot, STATISTICS_AFTER, newModel, INDEX_STATISTICS_AFTER, true, null);
			
			refresh();
			
			// after initializing the statistics need to be calculated
			calculateContent(oldModel, newModel, monitor);
		} else {
			// case: update
			if (isCanceled()) return;

			if (Runtime.getRuntime().availableProcessors() >= PROCESSOR_LIMIT) {
				// case: running in parallel jobs
		        // TODO it is unnecessary to refresh this every time while nothing has changed
				Job oldCalculationJob = new Job("Calculate: \"" + STATISTICS_BEFORE + "\"") {
					@Override
					protected IStatus run(IProgressMonitor monitor) {
						if (isCanceled()) return Status.OK_STATUS;
						monitor.beginTask("", 2);
						addStatistics(invisibleRoot, STATISTICS_BEFORE, oldModel, INDEX_STATISTICS_BEFORE, false, monitor);
						return Status.OK_STATUS;
					}
				};
				oldCalculationJob.setPriority(Job.DECORATE);
				oldCalculationJob.schedule();
				
				Job newCalculationJob = new Job("Calculate: \"" + STATISTICS_AFTER + "\"") {
					@Override
					protected IStatus run(IProgressMonitor monitor) {
						if (isCanceled()) return Status.OK_STATUS;
						monitor.beginTask("", 2);
						addStatistics(invisibleRoot, STATISTICS_AFTER, newModel, INDEX_STATISTICS_AFTER, false, monitor);
						return Status.OK_STATUS;
					}
				};
				newCalculationJob.setPriority(Job.DECORATE);
				newCalculationJob.schedule();
				
				setHeadAndExamples(monitor, oldModel, newModel);
				monitor.setTaskName("Waiting for subtasks to finish");
				try {
					oldCalculationJob.join();
					newCalculationJob.join();
					
				} catch (InterruptedException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			} else {
				// case: running in one jobs
				monitor.beginTask("Calculate content", 5);
				setHeadAndExamples(monitor, oldModel, newModel);
				if (isCanceled()) return;
				monitor.worked(1);

				// TODO it is unnecessary to refresh this every time while nothing has changed
				addStatistics(invisibleRoot, STATISTICS_BEFORE, oldModel, INDEX_STATISTICS_BEFORE, false, monitor);
				if (isCanceled()) return;
				addStatistics(invisibleRoot, STATISTICS_AFTER, newModel, INDEX_STATISTICS_AFTER, false, monitor);
			}		
		}
	}

	/**
	 * Sets the comparing entry and calculates some examples
	 * @param monitor
	 * @param oldModel 
	 * @param newModel 
	 */
	private void setHeadAndExamples(IProgressMonitor monitor, FeatureModel oldModel, FeatureModel newModel) {
		monitor.setTaskName("Compare models");
		TreeObject head = calculateHead(oldModel, newModel, comparator);
		TreeElement[] children = invisibleRoot.getChildren();
		((TreeObject)children[INDEX_HEAD]).setContents(head.getName(), head.getImage());
		((TreeObject)children[INDEX_ADDED]).set(new ExampleParent(true, comparator, 1, null));
		((TreeObject)children[INDEX_REMOVED]).set(new ExampleParent(false, comparator, 1, null));
		refresh();
	}

	/**
	 * Calculates the content of the first line
	 * Compares the old with the new model
	 */
	private TreeObject calculateHead(FeatureModel oldModel, FeatureModel newModel,
			ModelComparator comparator) {
		long start = System.currentTimeMillis();

		Comparison comparison = comparator.compare(oldModel, newModel);

		String message;
		Image image;
		if (comparison == Comparison.REFACTORING) {
			message = HEAD_REFACTORING;
			image = ZERO_IMAGE;
		} else if (comparison == Comparison.GENERALIZATION) {
			message = HEAD_GENERALIZATION;
			image = PLUS_IMAGE;
		} else if (comparison == Comparison.SPECIALIZATION) {
			message = HEAD_SPECIALIZATION;
			image = MINUS_IMAGE;
		} else if (comparison == Comparison.ARBITRARY) {
			message = HEAD_ARBITRARY;
			image = PLUS_MINUS_IMAGE;
		} else if (comparison == Comparison.OUTOFMEMORY) {
			message = HEAD_OUTOFMEMORY;
			image = ERROR_IMAGE_TSK;
		} else if (comparison == Comparison.TIMEOUT) {
			message = HEAD_TIME_OUT;
			image = ERROR_IMAGE_TSK;
		} else {
			message = HEAD_ERROR;
			image = ERROR_IMAGE_TSK;
		}

		message += " (" + (System.currentTimeMillis() - start) + "msec)";
		return new TreeObject(message, image);
	}

	/**
	 * Sets the statistics entries and counts the numbers of program variants and configurations
	 * @param root The root of the tree
	 * @param text The text of the statistics
	 * @param model The corresponding model 
	 * @param position The position of the statistics at the roots children
	 * @param init A flag which indicates if the statistics only should be initialized or if they should be calculated 
	 * @param monitor The monitor of the running job
	 */
	private void addStatistics(TreeParent root, final String text,
			final FeatureModel model, int position, boolean init, IProgressMonitor monitor) {
		if (monitor != null) {
			monitor.setTaskName("Calculate: \"" + text + "\"");
		}
		
		final int features = model.getNumberOfFeatures();
		final int constraints = model.getConstraintCount();
		final int concrete = model.getAnalyser().countConcreteFeatures();
		final int terminal = model.getAnalyser().countTerminalFeatures();
		final int hidden   = model.getAnalyser().countHiddenFeatures();
		
		if (init) {
			// case: init
			// does not count configurations and program variants
			TreeParent statistics = new TreeParent(text, null, true) {
				@Override
				public void initChildren() {
					try {
						addChild(MODEL_VOID + model.getAnalyser().isValid());
					} catch (TimeoutException e) {
						addChild(MODEL_TIMEOUT);
					}
					addChild(NUMBER_FEATURES + features);
					addChild(NUMBER_CONCRETE + concrete);
					addChild(NUMBER_ABSTRACT + (features - concrete));
					addChild(NUMBER_PRIMITIVE + terminal);
					addChild(NUMBER_COMPOUND + (features - terminal));
					addChild(NUMBER_HIDDEN + hidden);
					addChild(NUMBER_CONSTRAINTS + constraints);
					addChild(new TreeObject(CALCULATING_MESSAGE, DEFAULT_IMAGE));
					addChild(new TreeObject(CALCULATING_MESSAGE, DEFAULT_IMAGE));
				}
			};
			root.addChild(statistics);
		} else {
			// case: update
			// calculates the statistics
			TreeObject statistics = (TreeObject)root.getChildren()[position];
			final TreeElement[] children = statistics.getChildren();
			try {
				if (children[INDEX_VALID] instanceof SelectableFeature) {
					((SelectableFeature) children[INDEX_VALID]).setName(MODEL_VOID
							+ model.getAnalyser().isValid());
				} else {
					((TreeObject) children[INDEX_VALID]).setName(MODEL_VOID
							+ model.getAnalyser().isValid());
				}
			} catch (TimeoutException e) {
				if (children[INDEX_VALID] instanceof SelectableFeature) {
					((SelectableFeature) children[INDEX_VALID]).setName(MODEL_TIMEOUT);
				} else {
					((TreeObject)children[INDEX_VALID]).setName(MODEL_TIMEOUT);
				}
			} catch (ConcurrentModificationException e) {
				
			}
			((TreeObject)children[INDEX_FEATURES]).setName(NUMBER_FEATURES + features);
			((TreeObject)children[INDEX_CONCRETE]).setName(NUMBER_CONCRETE + concrete);
			((TreeObject)children[INDEX_ABSTRACT]).setName(NUMBER_ABSTRACT + (features - concrete));
			((TreeObject)children[INDEX_PRIMITIVE]).setName(NUMBER_PRIMITIVE + terminal);
			((TreeObject)children[INDEX_COMPOUND]).setName(NUMBER_COMPOUND + (features - terminal));
			((TreeObject)children[INDEX_HIDDEN]).setName(NUMBER_HIDDEN + hidden);
			((TreeObject)children[INDEX_CONSTRAINTS]).setName(NUMBER_CONSTRAINTS + constraints);
			
			if (isCanceled()) return;
			
			if (Runtime.getRuntime().availableProcessors() >= PROCESSOR_LIMIT) {
				Job job = new Job("Calculate: \"" + text + "\"") {
					@Override
					protected IStatus run(IProgressMonitor monitor) {
						monitor.setTaskName("Calculate number of configurations");
						((TreeObject)children[INDEX_CONFIGS]).set(calculateNumberOfVariants(model, true));
						refresh();
						return Status.OK_STATUS;
					}
				};
				job.setPriority(Job.DECORATE);
				job.schedule();
				
				monitor.setTaskName("Calculate number of program variants");
				
				((TreeObject)children[INDEX_VARIANTS]).set(calculateNumberOfVariants(model, false));
				refresh();
				monitor.worked(1);
				try {
					monitor.setTaskName("Waiting for subtask to finish");
					job.join();
					monitor.worked(1);
					monitor.done();
				} catch (InterruptedException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			} else {
				((TreeObject)children[INDEX_CONFIGS]).set(calculateNumberOfVariants(model, true));
				refresh();
				monitor.worked(1);
				if (isCanceled()) return;
				((TreeObject)children[INDEX_VARIANTS]).set(calculateNumberOfVariants(model, false));
				refresh();
				monitor.worked(1);
			}
		}
	}

	private TreeParent calculateNumberOfVariants(FeatureModel model,
			boolean ignoreAbstractFeatures) {
		
		String variants = ignoreAbstractFeatures ? "configurations"
				: "program variants";
		TreeParent p = new TreeParent("Number of " + variants, null, true) {
			@Override
			public void initChildren() {}
		};
		
		if (!ignoreAbstractFeatures && model.getAnalyser().countConcreteFeatures() == 0) {
			// case: there is no concrete feature so there is only one program variant,
			//       without this the calculation least much to long
			p.addChild("1 " + variants);
			return p;
		}
		final long number = new Configuration(model, false,
					ignoreAbstractFeatures).number(TIMEOUT_CONFIGURATION);			
		String s = "";
		if (number < 0)
			s += "more than " + (-1 - number);
		else
			s += number;
		s += " " + variants;
		p.addChild(s);
		return p;
	}
	
	/**
	 * Refreshes the tree in a fast running job with highest priority 
	 */
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

}
