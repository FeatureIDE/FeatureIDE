package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.ui.helper.JobDoneListener;
import de.ovgu.featureide.ui.statistics.ui.helper.TreeClickListener;
import de.ovgu.featureide.ui.statistics.ui.helper.jobs.StoppableTreeJob;

/**
 * Parent for the actual {@link ConfigNode}s.
 * 
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class ConfigParentNode extends LazyParent {
	private FeatureModel model;

	public static class ConfigNode extends Parent {
		private FeatureModel innerModel;

		public ConfigNode(String description, FeatureModel innerModel) {
			super(description, "(double-click to calculate)");
			this.innerModel = innerModel;
		}

		/**
		 * calculates the number of configurations/variants depending on
		 * ignoreAbstract. This method should be called by
		 * {@link TreeClickListener}.
		 * 
		 * @param timeout
		 *            defines how long the SAT-Solver may take to accomplish the
		 *            task.
		 * @param priority
		 *            for the job.
		 */
		public void calculate(final long timeout, final int priority) {
			Job job = new StoppableTreeJob("Calculating "
					+ this.description, this) {

				private String calculateConfigs() {
					boolean ignoreAbstract = description.equals(DESC_CONFIGS);
					if (!ignoreAbstract
							&& innerModel.getAnalyser().countConcreteFeatures() == 0) {
						// case: there is no concrete feature so there is only
						// one program
						// variant,
						// without this the calculation least much to long
						return "1";
					}

					final long number = new Configuration(innerModel, false,
							ignoreAbstract).number(timeout);

					String s = "";
					if (number < 0) {
						s += "more than " + (-1 - number);
					} else {
						s += number;
					}
					return s;
				}

				@Override
				protected IStatus execute(IProgressMonitor monitor) {
					setValue(calculateConfigs());
					return Status.OK_STATUS;
				}

			};
			job.setPriority(priority);
			JobDoneListener listener = JobDoneListener.getInstance();
			if (listener != null) {
				job.addJobChangeListener(listener);
			}
			job.schedule();
		}
	}

	public ConfigParentNode(String description, FeatureModel model) {
		super(description);
		this.model = model;
	}

	@Override
	protected void initChildren() {
		addChild(new ConfigNode(DESC_CONFIGS, model));
		addChild(new ConfigNode(DESC_VARIANTS, model));
	}
}
