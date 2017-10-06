/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.keyhandler;

import java.util.ArrayList;
import java.util.Map;

import org.eclipse.gef.KeyHandler;
import org.eclipse.gef.KeyStroke;
import org.eclipse.gef.ui.parts.GraphicalViewerKeyHandler;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.swt.events.KeyEvent;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelEditPart;

/**
 * The KeyHandler for the FeatureDiagramEditor. </br> At Manual-Layout: </br> to ensure that actions registered in {@link #createKeyBindings()} will be handled
 * first! default actions will be handled at last!
 *
 * Handles searching of features in the Tree. </br> At Automatic-Layout: run {@link GraphicalViewerKeyHandler} first
 *
 * @author Guenter Ulreich
 * @author Andy Koch
 * @author Marcus Pinnecke
 */
public class FeatureDiagramEditorKeyHandler extends KeyHandler implements IEventListener {

	private static final long timeoutThreshold = 750;
	private final IGraphicalFeatureModel featureModel;
	private final GraphicalViewerKeyHandler gvKeyHandler;
	private final KeyHandler alternativeKeyHandler;
	private final ScrollingGraphicalViewer viewer;

	private final ArrayList<String> featureList = new ArrayList<>();

	private int curIndex;
	private String curSearchString;
	private long lastTime;

	/**
	 * alternativeKeyHandler handles the KeyEvents, if the GraphicalViewerKeyHandler is active for auto-layout
	 */
	public FeatureDiagramEditorKeyHandler(ScrollingGraphicalViewer view, IGraphicalFeatureModel featureModel) {
		super();

		this.featureModel = featureModel;
		viewer = view;

		alternativeKeyHandler = new KeyHandler();
		gvKeyHandler = new GraphicalViewerKeyHandler(view);
		gvKeyHandler.setParent(alternativeKeyHandler);
		setParent(gvKeyHandler);
		lastTime = 0;

		resetFeatureList();
		featureModel.getFeatureModel().addListener(this);
	}

	@Override
	public boolean keyReleased(KeyEvent e) {
		return false;
	}

	/**
	 * use {@link GraphicalViewerKeyHandler} first if auto-layout is active handles the searching on the graph (depth-first, same way as in Outline)
	 */
	@Override
	public boolean keyPressed(KeyEvent e) {
		if (Character.isISOControl(e.character)) {
			if (featureModel.getLayout().hasFeaturesAutoLayout()) {
				return gvKeyHandler.keyPressed(e);
			} else {
				return super.keyPressed(e);
			}
		}

		final long currentTime = System.currentTimeMillis();
		if ((currentTime - lastTime) > timeoutThreshold) {
			curSearchString = "";
		}
		lastTime = currentTime;

		curIndex = updateIterator();

		if ((curSearchString.length() == 1) && (curSearchString.charAt(0) == Character.toLowerCase(e.character))) {
			curSearchString = "";
			curIndex = (curIndex + 1) % featureList.size();
		}
		curSearchString += Character.toLowerCase(e.character);

		final int foundIndex = search();
		if (foundIndex >= 0) {
			// select the new feature
			final IFeature curFeature = featureModel.getFeatureModel().getFeature(featureList.get(foundIndex));
			if (curFeature != null) {
				final Map<?, ?> editPartRegistry = viewer.getEditPartRegistry();
				final FeatureEditPart part = (FeatureEditPart) editPartRegistry.get(featureModel.getGraphicalFeature(curFeature));
				if (part != null) {
					viewer.setSelection(new StructuredSelection(part));
					viewer.reveal(part);
				}
				curIndex = foundIndex;
			}
		}

		return true;
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		resetFeatureList();
	}

	/**
	 * To handle 2 key handlers (otherwise there would be an action loop)</br> {@inheritDoc}
	 */
	@Override
	public void put(KeyStroke keystroke, IAction action) {
		alternativeKeyHandler.put(keystroke, action);
		super.put(keystroke, action);
	}

	private void resetFeatureList() {
		featureList.clear();
		featureList.addAll(Functional.toList(Functional.map(featureModel.getFeatureModel().getFeatures(), new Functional.IFunction<IFeature, String>() {

			@Override
			public String invoke(IFeature t) {
				return t.getName();
			}
		})));
		curSearchString = "";
		curIndex = 0;
	}

	private int search() {
		for (int i = curIndex, end = curIndex + featureList.size(); i < end; i++) {
			final String name = featureList.get(i % featureList.size());
			if (name.toLowerCase().startsWith(curSearchString)) {
				return i % featureList.size();
			}
		}
		return -1;
	}

	private int updateIterator() {
		final IStructuredSelection sel = (IStructuredSelection) viewer.getSelection();

		if ((sel.size() == 1) && !(sel.getFirstElement() instanceof ModelEditPart)) {
			final Object element = sel.getFirstElement();
			final String featureName;

			if (element instanceof FeatureEditPart) {
				featureName = ((FeatureEditPart) element).getModel().getObject().getName();
			} else if (element instanceof IFeature) {
				featureName = ((IFeature) element).getName();
			} else {
				return 0;
			}

			return (!featureName.equalsIgnoreCase(featureList.get(curIndex))) ? featureList.indexOf(featureName) : curIndex;
		}
		return 0;
	}

}
