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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.FOCUS_ON_EXPLANATION;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.action.Action;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.explanations.fm.FeatureModelExplanation;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FocusOnExplanationOperation;

/**
 * Action for collapsing all features but those affected by the active explanation.
 *
 * @author Timo G&uuml;nther
 */
public class FocusOnExplanationAction extends Action {

	/** The ID of this action. */
	public static final String ID = "de.ovgu.featureide.collapseallbutexplanation";

	/** The graphical feature model context. */
	private final IGraphicalFeatureModel fm;

	/** The currently active explanation. */
	private FeatureModelExplanation<?> explanation;

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param fm the graphical feature model context
	 */
	public FocusOnExplanationAction(IGraphicalFeatureModel fm) {
		super(FOCUS_ON_EXPLANATION);
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/monitor_obj.gif"));
		this.fm = fm;
		addActiveExplanationListener();
	}

	/**
	 * Adds a listener that updates the active explanation.
	 */
	private void addActiveExplanationListener() {
		fm.getFeatureModel().addListener(new IEventListener() {

			@Override
			public void propertyChange(FeatureIDEEvent event) {
				if (event.getEventType() != EventType.ACTIVE_EXPLANATION_CHANGED) {
					return;
				}
				setExplanation((FeatureModelExplanation<?>) event.getNewValue());
			}
		});
	}

	/**
	 * Returns the graphical feature model context.
	 *
	 * @return the graphical feature model context
	 */
	public IGraphicalFeatureModel getGraphicalFeatureModel() {
		return fm;
	}

	/**
	 * Returns the currently active explanation.
	 *
	 * @return the currently active explanation.
	 */
	public FeatureModelExplanation<?> getExplanation() {
		return explanation;
	}

	/**
	 * Sets the currently active explanation.
	 *
	 * @param explanation the new active explanation
	 */
	public void setExplanation(FeatureModelExplanation<?> explanation) {
		this.explanation = explanation;
		setEnabled(explanation != null);
	}

	@Override
	public void run() {
		final FocusOnExplanationOperation op = new FocusOnExplanationOperation(getGraphicalFeatureModel(), getExplanation());
		try {
			PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
		} catch (final ExecutionException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}
}
