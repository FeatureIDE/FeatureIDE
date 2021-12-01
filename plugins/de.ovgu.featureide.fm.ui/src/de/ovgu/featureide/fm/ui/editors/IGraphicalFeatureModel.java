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
package de.ovgu.featureide.fm.ui.editors;

import java.util.Collection;
import java.util.List;

import de.ovgu.featureide.fm.core.IGraphicItem;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.Legend;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureModelLayout;

/**
 * Graphical representation of a feature model.
 *
 * @author Sebastian Krieter
 * @author Thomas Graave
 * @author Rahel Arens
 */
public interface IGraphicalFeatureModel extends IGraphicItem, Cloneable {

	IFeatureModelManager getFeatureModelManager();

	/**
	 * @return True iff the initial feature model, e.g. when opening a file, contains layout information.
	 */
	boolean hasInitialLayout();

	FeatureModelLayout getLayout();

	boolean isLegendHidden();

	void setLegendHidden(boolean hidden);

	Legend getLegend();

	void setConstraintsHidden(boolean hideConstraints);

	boolean getConstraintsHidden();

	void handleLegendLayoutChanged();

	void handleModelLayoutChanged();

	void redrawDiagram();

	void refreshContextMenu();

	Collection<IGraphicalFeature> getFeatures();

	Collection<IGraphicalFeature> getAllFeatures();

	void setActiveExplanation(Explanation<?> exp);

	Explanation<?> getActiveExplanation();

	IGraphicalFeature getGraphicalFeature(IFeature newFeature);

	List<IGraphicalConstraint> getConstraints();

	IGraphicalConstraint getGraphicalConstraint(IConstraint newFeature);

	IGraphicalFeatureModel clone();

	void init();

	/**
	 * Returns the list of not collapsed constraints stored in this feature model. <br>Note: The returned list should be unmodifiable to avoid external access
	 * to internal data
	 *
	 * @see #getConstraintIndex(Constraint)
	 * @see #getVisibleConstraints()
	 * @see #getVisibleFeatures()
	 *
	 * @since 3.3
	 *
	 * @return All not collapsed constraints stored in this feature model.
	 */
	List<IGraphicalConstraint> getNonCollapsedConstraints();

	/**
	 * Returns getNonCollapsedConstraints only if the Constraints are not supposed to be hidden.
	 *
	 * @see #getNonCollapsedConstraints()
	 *
	 * @return All not collapsed constraints stored in this feature model that shall be shown in the feature model editor.
	 */
	List<IGraphicalConstraint> getVisibleConstraints();

	/**
	 * Returns the list of not collapsed features stored in this feature model. <br> <br> Note: The returned list should be unmodifiable to avoid external
	 * access to internal data
	 *
	 * @since 3.3
	 *
	 * @return All not collapsed constraints stored in this feature model.
	 */
	List<IGraphicalFeature> getVisibleFeatures();

	/**
	 * return the current index of the constraint. It will olny count constaints that are currently visible.
	 *
	 * @param constraint constraint to search
	 * @return index of constraint
	 */
	int getConstraintIndex(Constraint constraint);

	void writeValues();

	void writeFeatureModel();

	void writeConstraint(final IGraphicalConstraint graphicalConstraint);

	void writeFeature(final IGraphicalFeature graphicalFeature);

	void readValues();

	List<IGraphicalFeature> getVisibleRelations();

}
