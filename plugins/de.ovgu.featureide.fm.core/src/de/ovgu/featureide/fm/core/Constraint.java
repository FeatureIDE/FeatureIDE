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
package de.ovgu.featureide.fm.core;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Collection;

import org.prop4j.Node;
import org.prop4j.SatSolver;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.FeatureUtilsLegacy;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * Represents a propositional constraint below the feature diagram.
 *
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 */
@Deprecated
public class Constraint implements IGraphicItem {

	public Constraint(IFeatureModel featureModel, Node propNode) {
		throw new UnsupportedOperationException("No longer supported");
	}

	public Constraint(FeatureModel featureModel, Node propNode) {
		throw new UnsupportedOperationException("No longer supported");
	}

	public IConstraint constraint;

	public Constraint(IConstraint c) {
		constraint = c;
	}

	public void setLocation(FMPoint newLocation) {
		FeatureUtilsLegacy.setLocation(constraint, newLocation);
	}

	public FMPoint getLocation() {
		return FeatureUtilsLegacy.getLocation(constraint);
	}

	public FeatureModel getFeatureModel() {
		return FeatureUtilsLegacy.convert(FeatureUtils.getFeatureModel(constraint));
	}

	public Collection<Feature> getDeadFeatures(SatSolver solver, FeatureModel fm, Collection<Feature> fmDeadFeatures) {
		return Functional.toList(Functional.map(FeatureUtils.getDeadFeatures(constraint, solver, FeatureUtilsLegacy.convert(fm),
				Functional.toList(Functional.map(fmDeadFeatures, FeatureUtilsLegacy.FEATURE_TO_IFEATURE))), FeatureUtilsLegacy.IFEATURE_TO_FEATURE));
	}

	public Collection<Feature> getDeadFeatures(FeatureModel fm, Collection<Feature> fmDeadFeatures) {
		return Functional.toList(Functional.map(FeatureUtils.getDeadFeatures(constraint, FeatureUtilsLegacy.convert(fm),
				Functional.toList(Functional.map(fmDeadFeatures, FeatureUtilsLegacy.FEATURE_TO_IFEATURE))), FeatureUtilsLegacy.IFEATURE_TO_FEATURE));
	}

	public void setConstraintAttribute(ConstraintAttribute attri, boolean fire) {
		FeatureUtils.setConstraintAttribute(constraint, attri, fire);
	}

	public ConstraintAttribute getConstraintAttribute() {
		return FeatureUtils.getConstraintAttribute(constraint);
	}

	public Node getNode() {
		return FeatureUtils.getNode(constraint);
	}

	public void setContainedFeatures() {
		FeatureUtils.setContainedFeatures(constraint);
	}

	public Collection<Feature> getContainedFeatures() {
		return Functional.toList(Functional.map(FeatureUtils.getContainedFeatures(constraint), FeatureUtilsLegacy.IFEATURE_TO_FEATURE));
	}

	public boolean setFalseOptionalFeatures(FeatureModel clone, Collection<Feature> fmFalseOptionals) {
		return FeatureUtils.setFalseOptionalFeatures(constraint, FeatureUtilsLegacy.convert(clone),
				Functional.toList(Functional.map(fmFalseOptionals, FeatureUtilsLegacy.FEATURE_TO_IFEATURE)));
	}

	public boolean setFalseOptionalFeatures() {
		return FeatureUtils.setFalseOptionalFeatures(constraint);
	}

	public Collection<Feature> getFalseOptional() {
		return Functional.toList(Functional.map(FeatureUtils.getFalseOptional(constraint), FeatureUtilsLegacy.IFEATURE_TO_FEATURE));
	}

	public void addListener(PropertyChangeListener listener) {
		FeatureUtils.addListener(constraint, listener);
	}

	public void removeListener(PropertyChangeListener listener) {
		FeatureUtils.removeListener(constraint, listener);
	}

	public void fire(PropertyChangeEvent event) {
		FeatureUtils.fire(constraint, event);
	}

	@Override
	public int hashCode() {
		return FeatureUtils.hashCode(constraint);
	};

	@Override
	public boolean equals(Object obj) {
		return FeatureUtils.equals(constraint, obj);
	}

	@Override
	public String toString() {
		return FeatureUtils.toString(constraint);
	}

	public boolean hasHiddenFeatures() {
		return FeatureUtils.hasHiddenFeatures(constraint);
	}

	public void setDeadFeatures(Collection<Feature> deadFeatures) {
		FeatureUtils.setDeadFeatures(constraint, Functional.toList(Functional.map(deadFeatures, FeatureUtilsLegacy.FEATURE_TO_IFEATURE)));
	}

	public Collection<Feature> getDeadFeatures() {
		return Functional.toList(Functional.map(FeatureUtils.getDeadFeatures(constraint), FeatureUtilsLegacy.IFEATURE_TO_FEATURE));
	}

	@Override
	public GraphicItem getItemType() {
		return FeatureUtils.getItemType(constraint);
	}

}
