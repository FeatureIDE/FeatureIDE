/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io.manager;

import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * Responsible to load and save all information for a feature model instance.
 *
 * @author Sebastian Krieter
 */
public interface IFeatureModelManager extends IManager<IFeatureModel> {

	/**
	 * Returns the modifiable undo-context of this feature model. To undo-context enables undoing of actions performed to this feature model, such as renaming
	 * or feature removing over the user interface. The undo context is intended to work seamlessly with the eclipse framework used, e.g., in the feature model
	 * diagram editor.
	 *
	 * @since 3.0
	 *
	 * @see #setUndoContext(Object)
	 *
	 * @return undo-context of this feature model
	 */
	Object getUndoContext();

	/**
	 * Sets the modifiable undo-context of this feature model. To undo-context enables undoing of actions performed to this feature model, such as renaming or
	 * feature removing over the user interface. The undo context is intended to work seamlessly with the eclipse framework used, e.g., in the feature model
	 * diagram editor.
	 *
	 * @since 3.0
	 *
	 * @see #getUndoContext()
	 *
	 * @param undoContext
	 */
	void setUndoContext(Object undoContext);

	ProblemList getLastProblems();

	ProblemList read();

	ProblemList readFromSource(CharSequence newText);

	FeatureModelFormula getPersistentFormula();

	FeatureModelFormula getVariableFormula();

	/**
	 * Inform all feature models that import the current feature model that the event <code>e</code> occurred.
	 *
	 * @param e - {@link FeatureIDEEvent}
	 */
	public void informImports(FeatureIDEEvent e);

}
