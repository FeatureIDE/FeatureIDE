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
import java.util.LinkedList;
import java.util.List;

import javax.annotation.CheckForNull;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.FeatureUtilsLegacy;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.IPropertyContainer;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * <b>This class is deprecated and only existing due to compatibility considerations</b>. Use {@link de.ovgu.featureide.fm.core.base.impl.Feature new Feature
 * class} instead.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 *
 * @see IFeature Interface for features (<code>IFeature</code>)
 * @see de.ovgu.featureide.fm.core.base.impl.Feature Default implementation of interface for features (<code>Feature</code>) since version 3.0
 * @see IConstraint Interface for feature constraints (<code>IConstraint</code>)
 * @see IFeatureModel Interface for feature models (<code>IFeatureModel</code>)
 * @see IFeatureProperty Interface for feature properties (<code>IFeatureProperty</code>)
 * @see IFeatureStructure Interface for a feature's structure (<code>IFeatureStructure</code>)
 */
@Deprecated
public class Feature implements PropertyChangeListener, IGraphicItem, IFeature {

	public final IFeature feature;

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getDescription(IFeature); </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@CheckForNull
	@Deprecated
	public String getDescription() {
		return FeatureUtils.getDescription(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setDescription(IFeature, CharSequence) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setDescription(String description) {
		FeatureUtils.setDescription(feature, description);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> <i>This
	 * constructor is a bridge to the IFeature interface and establish the delegation. This method should not be used by third party.</i>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public Feature(IFeature feature) {
		this.feature = feature;
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setNewLocation(IFeature, FMPoint); </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	public void setNewLocation(FMPoint newLocation) {
		FeatureUtilsLegacy.setNewLocation(feature, newLocation);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getLocation(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public FMPoint getLocation() {
		return FeatureUtilsLegacy.getLocation(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isAnd(IFeature); </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isAnd() {
		return FeatureUtils.isAnd(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> IFeature.getStructure().isOr(); </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isOr() {
		return FeatureUtils.isOr(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isAlternative(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isAlternative() {
		return FeatureUtils.isAlternative(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.changeToAnd(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void changeToAnd() {
		FeatureUtils.changeToAnd(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.changeToOr(IFeature); </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void changeToOr() {
		FeatureUtils.changeToOr(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.changeToAlternative(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void changeToAlternative() {
		FeatureUtils.changeToAlternative(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setAnd(IFeature, boolean) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setAND(boolean and) {
		FeatureUtils.setAnd(feature, and);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isMandatorySet(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isMandatorySet() {
		return FeatureUtils.isMandatorySet(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isMandatory(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isMandatory() {
		return FeatureUtils.isMandatory(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setMandatory(IFeature, boolean) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setMandatory(boolean mandatory) {
		FeatureUtils.setMandatory(feature, mandatory);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isHidden(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isHidden() {
		return FeatureUtils.isHidden(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setHiddden(IFeature, boolean) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setHidden(boolean hid) {
		FeatureUtils.setHiddden(feature, hid);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isConstraintSelected(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isConstraintSelected() {
		return FeatureUtils.isConstraintSelected(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> IFeature.getStructure().selectConstraint(selection); </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	public void setConstraintSelected(boolean selection) {
		FeatureUtils.setConstraintSelected(feature, selection);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setAbstract(IFeature, boolean) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setAbstract(boolean value) {
		FeatureUtils.setAbstract(feature, value);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getRelevantConstraints(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public Collection<IConstraint> getRelevantConstraints() {
		return FeatureUtils.getRelevantConstraints(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getRelevantConstraintsString(IFeature, IFeatureModel).getConstraints()); </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public String getRelevantConstraintsString() {
		return FeatureUtils.getRelevantConstraintsString(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setRelevantConstraints(feature); </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setRelevantConstraints() {
		FeatureUtils.setRelevantConstraints(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getFeatureStatus(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public FeatureStatus getFeatureStatus() {
		return FeatureUtils.getFeatureStatus(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getFeatureModel(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Override
	@Deprecated
	public IFeatureModel getFeatureModel() {
		return FeatureUtils.getFeatureModel(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setFeatureStatus(IFeature, FeatureStatus, boolean); </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setFeatureStatus(FeatureStatus stat, boolean fire) {
		FeatureUtils.setFeatureStatus(feature, stat, fire);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isMultiple(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isMultiple() {
		return FeatureUtils.isMultiple(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setMultiple(IFeature, boolean) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setMultiple(boolean multiple) {
		FeatureUtils.setMultiple(feature, multiple);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getName(Feature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Override
	@Deprecated
	public String getName() {
		return FeatureUtils.getName(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setName(feature, name) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Override
	@Deprecated
	public void setName(String name) {
		FeatureUtils.setName(feature, name);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.hasInlineRule(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean hasInlineRule() {
		return FeatureUtils.hasInlineRule(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setParent(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setParent(Feature newParent) {
		FeatureUtils.setParent(feature, newParent.feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getParent(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public Feature getParent() {
		return FeatureUtilsLegacy.convert(FeatureUtils.getParent(feature));
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isRoot(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isRoot() {
		return FeatureUtils.isRoot(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> IFeature.getStructure().getChildren(); </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public LinkedList<Feature> getChildren() {
		return new LinkedList<>(Functional.toList(Functional.map(FeatureUtils.getChildren(feature), FeatureUtilsLegacy.IFEATURE_TO_FEATURE)));
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setChildren(IFeature, Iterable) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setChildren(LinkedList<Feature> children) {
		FeatureUtils.setChildren(feature, Functional.map(children, FeatureUtilsLegacy.FEATURE_TO_IFEATURE));
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.hasChildren(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean hasChildren() {
		return FeatureUtils.hasChildren(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.addChild(IFeature, IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void addChild(Feature newChild) {
		FeatureUtils.addChild(feature, newChild.feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.addChildAtPosition(IFeature, int, IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void addChildAtPosition(int index, Feature newChild) {
		FeatureUtils.addChildAtPosition(feature, index, newChild.feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.replaceChild(IFeature, IFeature, IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void replaceChild(Feature oldChild, Feature newChild) {
		FeatureUtils.replaceChild(feature, oldChild.feature, newChild.feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.removeChild(IFeature, IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void removeChild(Feature child) {
		FeatureUtils.removeChild(feature, child.feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.removeLastChild(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public Feature removeLastChild() {
		return FeatureUtilsLegacy.convert(FeatureUtils.removeLastChild(feature));
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getSourceConnections(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public List<FeatureConnection> getSourceConnections() {
//		return Functional.toList(FeatureUtils.getSourceConnections(feature));
		return null;
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getTargetConnections(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public List<FeatureConnection> getTargetConnections() {
//		return Functional.toList(FeatureUtils.getTargetConnections(feature));
		return null;
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.addTargetConnection(IFeature, FeatureConnection) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void addTargetConnection(FeatureConnection connection) {
//		FeatureUtils.addTargetConnection(feature, connection);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.removeTargetConnection(IFeature, FeatureConnection) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean removeTargetConnection(FeatureConnection connection) {
//		return FeatureUtils.removeTargetConnection(feature, connection);
		return false;
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.addListener(IFeature, PropertyChangeListener); </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void addListener(PropertyChangeListener listener) {
		FeatureUtils.addListener(feature, listener);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.removeListener(IFeature, PropertyChangeListener); </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void removeListener(PropertyChangeListener listener) {
		FeatureUtils.removeListener(feature, listener);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isAncestorOf(IFeature, IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isAncestorOf(Feature next) {
		return FeatureUtils.isAncestorOf(feature, next.feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isFirstChild(IFeature, IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isFirstChild(Feature child) {
		return FeatureUtils.isFirstChild(feature, child.feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getChildrenCount(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public int getChildrenCount() {
		return FeatureUtils.getChildrenCount(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getFirstChild(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public Feature getFirstChild() {
		return new Feature(FeatureUtils.getFirstChild(feature));
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getLastChild(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public Feature getLastChild() {
		return new Feature(FeatureUtils.getLastChild(feature));
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getChildIndex(IFeature, IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public int getChildIndex(Feature child) {
		return FeatureUtils.getChildIndex(feature, FeatureUtilsLegacy.convert(child));
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isAbstract(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isAbstract() {
		return FeatureUtils.isAbstract(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isConcrete(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isConcrete() {
		return FeatureUtils.isConcrete(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.isANDPossible(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean isANDPossible() {
		return FeatureUtils.isANDPossible(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.fire(IFeature, PropertyChangeEvent) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void fire(PropertyChangeEvent event) {
		FeatureUtils.fire(feature, event);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.clone(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	@Override
	public Feature clone() {
		return new Feature(FeatureUtils.clone(feature));
	}

	public Feature clone(IFeatureModel featureModel, boolean complete) {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setAnd(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setAnd() {
		FeatureUtils.setAnd(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setOr(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setOr() {
		FeatureUtils.setOr(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.setAlternative(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public void setAlternative() {
		FeatureUtils.setAlternative(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.hasHiddenParent(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public boolean hasHiddenParent() {
		return FeatureUtils.hasHiddenParent(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.toString(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	@Override
	public String toString() {
		return FeatureUtils.toString(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getDisplayName(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public String getDisplayName() {
		return FeatureUtils.getDisplayName(feature);
	}

	@Override
	public void propertyChange(PropertyChangeEvent event) {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Deprecated
	public String toString(boolean writeMarks) {
		if (writeMarks) {
			if (feature.getName().contains(" ") || Operator.isOperatorName(feature.getName())) {
				return "\"" + feature.getName() + "\"";
			}
			return feature.getName();
		} else {
			return toString();
		}
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getColorList(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	public ColorList getColorList() {
//		return FeatureUtils.getColorList(feature);
		return null;
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.hashCode(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	@Override
	public int hashCode() {
		return FeatureUtils.hashCode(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b> </br>Internally, the
	 * <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying {@link IFeature IFeature interface}.<br/><br/> Instead of this
	 * method you should use<br/> <code> FeatureUtils.getItemType(IFeature) </code>
	 *
	 * @author Marcus Pinnecke
	 * @since 2.7.5
	 */
	@Deprecated
	@Override
	public GraphicItem getItemType() {
		return FeatureUtils.getItemType(feature);
	}

	@Override
	public long getInternalId() {
		return feature.getInternalId();
	}

	@Override
	public void addListener(IEventListener listener) {
		feature.addListener(listener);
	}

	@Override
	public void fireEvent(FeatureIDEEvent event) {
		feature.fireEvent(event);
	}

	@Override
	public void removeListener(IEventListener listener) {
		feature.removeListener(listener);
	}

	@Override
	public IFeature clone(IFeatureModel newFeatureModel, IFeatureStructure newStructure) {
		return feature.clone(newFeatureModel, newStructure);
	}

	@Override
	public IFeatureProperty getProperty() {
		return feature.getProperty();
	}

	@Override
	public IPropertyContainer getCustomProperties() {
		return feature.getCustomProperties();
	}

	@Override
	public IFeatureStructure getStructure() {
		return feature.getStructure();
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.base.IFeature#createTooltip(java.lang.Object[])
	 */
	@Override
	public String createTooltip(Object... objects) {
		return "No tooltip implementation.";
	}
}
