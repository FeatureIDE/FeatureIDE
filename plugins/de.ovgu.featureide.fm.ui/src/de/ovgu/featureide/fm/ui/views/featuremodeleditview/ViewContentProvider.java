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
package de.ovgu.featureide.fm.ui.views.featuremodeleditview;

import java.util.ConcurrentModificationException;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.TreeElement;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.views.FeatureModelEditView;

/**
 * Calculates the edit category and provides as a content to the view.
 * 
 * @author Thomas Thuem
 */
public class ViewContentProvider implements IStructuredContentProvider,
		ITreeContentProvider, GUIDefaults {

	private static final String DEFAULT_MESSAGE = "Open a feature model.";
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
	protected static final String MODEL_VOID = "Feature model is valid (not void): ";
	protected static final String MODEL_TIMEOUT = MODEL_VOID + "timeout";
	
	private static final String STATISTICS_BEFORE = "Statistics on before edit version";
	private static final String STATISTICS_AFTER = "Statistics on after edit version";	
	
	/**
	 * time in seconds after the calculation is aborted by the SAT solver
	 */
	private static final int TIMEOUT = 20000;

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

	public void defaultContent() {
		invisibleRoot.setChild(new TreeObject(DEFAULT_MESSAGE, DEFAULT_IMAGE));
		refresh();
	}

	private int i;
	private FeatureModel model;
	
	public void calculateContent(FeatureModel oldModel, FeatureModel newModel) {
		if (oldModel.getRoot() == null || newModel.getRoot() == null)
			return;
		i = 0;
		ModelComparator comparator = new ModelComparator(TIMEOUT);
		if (invisibleRoot.getChildren().length < 1) {
			invisibleRoot.addChild(new TreeObject(CALCULATING_MESSAGE, DEFAULT_IMAGE));
		} else {
			((TreeObject)invisibleRoot.getChildren()[i]).setContents(CALCULATING_MESSAGE, DEFAULT_IMAGE);
		}
		refresh();
		TreeObject head = calculateHead(oldModel, newModel, comparator);
		((TreeObject)invisibleRoot.getChildren()[i++]).setContents(head.getName(), head.getImage());
		
		if (invisibleRoot.getChildren().length < 2) {
			invisibleRoot.addChild("");
			invisibleRoot.addChild(new ExampleParent(true, comparator, 1, null));
			invisibleRoot.addChild(new ExampleParent(false, comparator, 1, null));
			invisibleRoot.addChild("");
		} else  {
			i++;
			((TreeObject)invisibleRoot.getChildren()[i++]).set(new ExampleParent(true, comparator, 1, null));
			((TreeObject)invisibleRoot.getChildren()[i++]).set(new ExampleParent(false, comparator, 1, null));
			i++;
		}
		addStatistics(invisibleRoot, STATISTICS_BEFORE,
				oldModel);
		addStatistics(invisibleRoot, STATISTICS_AFTER,
				newModel);
		refresh();
	}

	/**
	 * 
	 */
	private TreeObject calculateHead(FeatureModel oldModel, FeatureModel newModel,
			ModelComparator comparator) {
		long start = System.nanoTime();

		
		Comparison comparison = comparator.compare(oldModel, newModel);

		String message = null;
		Image image = null;
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

		message += " (" + (System.nanoTime() - start) / 1000000 + "msec)";
		return new TreeObject(message, image);
	}

	private void addStatistics(TreeParent statistics, String text,
			final FeatureModel model) {
		final int features = model.getNumberOfFeatures();
		final int concrete = model.countConcreteFeatures();
		final int terminal = model.countTerminalFeatures();
		final int hidden   = model.countHiddenFeatures();
		
		if (statistics.getChildren().length < i ||
				statistics.getChildren()[i].getChildren().length < 1) {
			TreeParent parent = new TreeParent(text, null, true) {
				@Override
				public void initChildren() {
					try {
						addChild(MODEL_VOID
								+ model.isValid());
					} catch (TimeoutException e) {
						addChild(MODEL_TIMEOUT);
					}
					addChild(NUMBER_FEATURES + features);
					addChild(NUMBER_CONCRETE + concrete);
					addChild(NUMBER_ABSTRACT + (features - concrete));
					addChild(NUMBER_PRIMITIVE + terminal);
					addChild(NUMBER_COMPOUND + (features - terminal));
					addChild(NUMBER_HIDDEN + hidden);
					addChild(calculateNumberOfVariants(model, true));
					addChild(calculateNumberOfVariants(model, false));
				}
			};
			statistics.addChild(parent);
		} else {
			TreeObject parent = (TreeObject)statistics.getChildren()[i];
			int i = 0;
			try {
				if (parent.getChildren()[i] instanceof SelectableFeature) {
					((SelectableFeature) parent.getChildren()[i]).setName(MODEL_VOID
							+ model.isValid());
				} else {
					((TreeObject) parent.getChildren()[i]).setName(MODEL_VOID
							+ model.isValid());
				}
			} catch (TimeoutException e) {
				if (parent.getChildren()[i] instanceof SelectableFeature) {
					((SelectableFeature) parent.getChildren()[i]).setName(MODEL_TIMEOUT);
				} else {
					((TreeObject)parent.getChildren()[i]).setName(MODEL_TIMEOUT);
				}
			} catch (ConcurrentModificationException e) {
				
			}
			((TreeObject)parent.getChildren()[++i]).setName(NUMBER_FEATURES + features);
			((TreeObject)parent.getChildren()[++i]).setName(NUMBER_CONCRETE + concrete);
			((TreeObject)parent.getChildren()[++i]).setName(NUMBER_ABSTRACT + (features - concrete));
			((TreeObject)parent.getChildren()[++i]).setName(NUMBER_PRIMITIVE + terminal);
			((TreeObject)parent.getChildren()[++i]).setName(NUMBER_COMPOUND + (features - terminal));
			((TreeObject)parent.getChildren()[++i]).setName(NUMBER_HIDDEN + hidden);
			((TreeObject)parent.getChildren()[++i]).set(calculateNumberOfVariants(model, true));
			((TreeObject)parent.getChildren()[++i]).set(calculateNumberOfVariants(model, false));
		}
		i++;
	}

	private FeatureModel getModel() {
		return model;
	}
	private TreeParent calculateNumberOfVariants(
			final FeatureModel model,
			final boolean ignoreAbstractFeatures) {
		this.model = model;
		final String variants = ignoreAbstractFeatures ? "configurations"
				: "program variants";
		return new TreeParent("Number of " + variants, null, true) {
			@Override
			public void initChildren() {
				removeChildren();
				long number = new Configuration(getModel(), false,
						ignoreAbstractFeatures).number(1000);
				String s = "";
				if (number < 0)
					s += "more than " + (-1 - number);
				else
					s += number;
				s += " " + variants;
				addChild(s);
			}
		};
	}

	private void refresh() {
		Display.getDefault().asyncExec(new Runnable() {
			public void run() {
				if (!view.getViewer().getControl().isDisposed()) {
					view.getViewer().refresh();
				}
			}
		});
	}

}
