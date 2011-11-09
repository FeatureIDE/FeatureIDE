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

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Display;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
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

	public void calculateContent(FeatureModel oldModel, FeatureModel newModel) {
		if (oldModel.getRoot() == null || newModel.getRoot() == null)
			return;

		invisibleRoot.setChild(new TreeObject(CALCULATING_MESSAGE,
				DEFAULT_IMAGE));
		refresh();

		long start = System.nanoTime();

		ModelComparator comparator = new ModelComparator(TIMEOUT);
		Comparison comparison = comparator.compare(oldModel, newModel);

		String message = null;
		Image image = null;
		if (comparison == Comparison.REFACTORING) {
			message = "Refactoring: SPL unchanged";
			image = ZERO_IMAGE;
		} else if (comparison == Comparison.GENERALIZATION) {
			message = "Generalization: Products added";
			image = PLUS_IMAGE;
		} else if (comparison == Comparison.SPECIALIZATION) {
			message = "Specialization: Products removed";
			image = MINUS_IMAGE;
		} else if (comparison == Comparison.ARBITRARY) {
			message = "Arbitrary edit: Products added and removed";
			image = PLUS_MINUS_IMAGE;
		} else if (comparison == Comparison.OUTOFMEMORY) {
			message = "Out of memory error!";
			image = ERROR_IMAGE_TSK;
		} else if (comparison == Comparison.TIMEOUT) {
			message = "SAT4J time out!";
			image = ERROR_IMAGE_TSK;
		} else {
			message = "An error has occured!";
			image = ERROR_IMAGE_TSK;
		}

		message += " (" + (System.nanoTime() - start) / 1000000 + "msec)";
		TreeObject result = new TreeObject(message, image);
		invisibleRoot.setChild(result);

		invisibleRoot.addChild("");
		invisibleRoot.addChild(new ExampleParent(true, comparator, 1));
		invisibleRoot.addChild(new ExampleParent(false, comparator, 1));

		invisibleRoot.addChild("");
		addStatistics(invisibleRoot, "Statistics on before edit version",
				oldModel);
		addStatistics(invisibleRoot, "Statistics on after edit version",
				newModel);

		refresh();
	}

	private void addStatistics(TreeParent statistics, String text,
			final FeatureModel model) {
		TreeParent parent = new TreeParent(text, null, true) {
			@Override
			public void initChildren() {
				int features = model.getNumberOfFeatures();
				int concrete = model.countConcreteFeatures();
				int terminal = model.countTerminalFeatures();

				try {
					addChild("Featur model is valid (not void): "
							+ model.isValid());
				} catch (TimeoutException e) {
					addChild("Featur model is valid (not void): timeout");
				}
				addChild("Number of features: " + features);
				addChild("Number of concrete features: " + concrete);
				addChild("Number of abstract features: "
						+ (features - concrete));
				addChild("Number of primitive features: " + terminal);
				addChild("Number of compound features: "
						+ (features - terminal));
				addChild(calculateNumberOfVariants(model, true));
				addChild(calculateNumberOfVariants(model, false));
			}

		};
		statistics.addChild(parent);
	}

	private TreeParent calculateNumberOfVariants(
			final FeatureModel model,
			final boolean ignoreAbstractFeatures) {
		final String variants = ignoreAbstractFeatures ? "configurations"
				: "program variants";
		return new TreeParent("Number of " + variants, null, true) {
			@Override
			public void initChildren() {
				long number = new Configuration(model, false,
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
