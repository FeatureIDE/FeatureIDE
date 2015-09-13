/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.UNKNOWN;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import javax.annotation.CheckForNull;

import org.prop4j.NodeWriter;

import de.ovgu.featureide.fm.core.ColorList;
import de.ovgu.featureide.fm.core.FMPoint;
import de.ovgu.featureide.fm.core.FeatureConnection;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.IGraphicItem;
import de.ovgu.featureide.fm.core.Operator;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.IGraphicItem.GraphicItem;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Provides all properties of a feature. This includes its connections to parent
 * and child features.
 * 
 * @author Thomas Thuem
 * 
 */
public class Feature implements PropertyConstants, PropertyChangeListener, IGraphicItem {

	private final IFeature feature;

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getProperty().getDescription()
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@CheckForNull
	@Deprecated
	public String getDescription() {
		return feature.getProperty().getDescription();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * feature.getProperty().setDescription(String)
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setDescription(String description) {
		feature.getProperty().setDescription(description);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * <i>This constructor is a bridge to the IFeature interface and establish the delegation. This method should not be used by third party.</i> 
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public Feature(IFeature feature) {
		this.feature = feature;
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getGraphicRepresenation().setNewLocation(FMPoint);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	public void setNewLocation(FMPoint newLocation) {
		feature.getGraphicRepresenation().setNewLocation(newLocation);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getLocation();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public FMPoint getLocation() {
		return feature.getLocation();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isAnd();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isAnd() {
		return feature.getStructure().isAnd();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isOr();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isOr() {
		return feature.getStructure().isOr();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isAlternative();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isAlternative() {
		return feature.getStructure().isAlternative();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().changeToAnd();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void changeToAnd() {
		feature.getStructure().changeToAnd();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().changeToOr();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void changeToOr() {
		feature.getStructure().changeToOr();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().changeToAlternative();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void changeToAlternative() {
		feature.getStructure().changeToAlternative();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().setAND(and);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setAND(boolean and) {
		feature.getStructure().setAND(and);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isMandatorySet();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isMandatorySet() {
		return feature.getStructure().isMandatorySet();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isMandatory();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isMandatory() {
		return feature.getStructure().isMandatory();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().setMandatory(mandatory);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setMandatory(boolean mandatory) {
		feature.getStructure().setMandatory(mandatory);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isHidden();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isHidden() {
		return feature.getStructure().isHidden();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().setHidden(hid);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setHidden(boolean hid) {
		feature.getStructure().setHidden(hid);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isConstraintSelected();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isConstraintSelected() {
		return feature.getStructure().isConstraintSelected();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().selectConstraint(selection);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	public void setConstraintSelected(boolean selection) {
		return feature.getStructure().selectConstraint(selection);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().setAbstract(value);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setAbstract(boolean value) {
		feature.getStructure().setAbstract(value);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().getRelevantConstraints();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public Collection<IConstraint> getRelevantConstraints() {
		feature.getStructure().getRelevantConstraints();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * FeatureUtils.getRelevantConstraintsString(IFeature, IFeatureModel).getConstraints());
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public String getRelevantConstraintsString() {
		return FeatureUtils.getRelevantConstraintsString(feature, feature.getFeatureModel().getConstraints());
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * FeatureUtils.setRelevantConstraints(feature);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setRelevantConstraints() {
		FeatureUtils.setRelevantConstraints(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getProperty().getFeatureStatus();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public FeatureStatus getFeatureStatus() {
		return feature.getProperty().getFeatureStatus();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getFeatureModel();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public IFeatureModel getFeatureModel() {
		return feature.getFeatureModel();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getProperty().setFeatureStatus(stat, fire);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setFeatureStatus(FeatureStatus stat, boolean fire) {
		return feature.getProperty().setFeatureStatus(stat, fire);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isMultiple();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isMultiple() {
		return feature.getStructure().isMultiple();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().setMultiple(multiple);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setMultiple(boolean multiple) {
		feature.getStructure().setMultiple(multiple);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getName();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public String getName() {
		return feature.getName();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.setName(name);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setName(String name) {
		feature.setName(name);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().hasInlineRule();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean hasInlineRule() {
		return feature.getStructure().hasInlineRule();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().setParent(newParent);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setParent(Feature newParent) {
		feature.getStructure().setParent(newParent);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().getParent();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public Feature getParent() {
		return feature.getStructure().getParent();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isRoot();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isRoot() {
		return feature.getStructure().isRoot();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().getChildren();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public LinkedList<Feature> getChildren() {
		return feature.getStructure().getChildren();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().setChildren(children);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setChildren(LinkedList<Feature> children) {
		return feature.getStructure().setChildren(children);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().hasChildren();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean hasChildren() {
		return feature.getStructure().hasChildren();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().addChild(newChild.feature.getStructure());
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void addChild(Feature newChild) {
		return feature.getStructure().addChild(newChild.feature.getStructure());
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().addChildAtPosition(index, newChild);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void addChildAtPosition(int index, Feature newChild) {
		feature.getStructure().addChildAtPosition(index, newChild);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().replaceChild(oldChild, newChild);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void replaceChild(Feature oldChild, Feature newChild) {
		feature.getStructure().replaceChild(oldChild, newChild);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().removeChild(child);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void removeChild(Feature child) {
		feature.getStructure().removeChild(child);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().removeLastChild();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public Feature removeLastChild() {
		feature.getStructure().removeLastChild();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().getSourceConnections();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public List<FeatureConnection> getSourceConnections() {
		return feature.getStructure().getSourceConnections();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().getTargetConnections();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public List<FeatureConnection> getTargetConnections() {
		return feature.getStructure().getTargetConnections();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().addTargetConnection(connection);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void addTargetConnection(FeatureConnection connection) {
		feature.getStructure().addTargetConnection(connection);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().removeTargetConnection(connection);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean removeTargetConnection(FeatureConnection connection) {
		feature.getStructure().removeTargetConnection(connection);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.addListener(listener);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void addListener(PropertyChangeListener listener) {
		feature.addListener(listener);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.removeListener(listener);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void removeListener(PropertyChangeListener listener) {
		feature.removeListener(listener);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.fireEvent(new PropertyChangeEvent(this, NAME_CHANGED, Boolean.FALSE, Boolean.TRUE));
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	private void fireNameChanged() {
		feature.fireEvent(new PropertyChangeEvent(this, NAME_CHANGED, Boolean.FALSE, Boolean.TRUE));
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.fireEvent(new PropertyChangeEvent(this, HIDDEN_CHANGED, Boolean.FALSE, Boolean.TRUE));
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	private void fireHiddenChanged() {
		feature.fireEvent(new PropertyChangeEvent(this, HIDDEN_CHANGED, Boolean.FALSE, Boolean.TRUE));
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.fireEvent(new PropertyChangeEvent(this, CHILDREN_CHANGED, Boolean.FALSE, Boolean.TRUE));
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	private void fireChildrenChanged() {
		feature.fireEvent(new PropertyChangeEvent(this, CHILDREN_CHANGED, Boolean.FALSE, Boolean.TRUE));
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.fireEvent(new PropertyChangeEvent(this, MANDATORY_CHANGED, Boolean.FALSE, Boolean.TRUE));
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	private void fireMandatoryChanged() {
		feature.fireEvent(new PropertyChangeEvent(this, MANDATORY_CHANGED, Boolean.FALSE, Boolean.TRUE));
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isAncestorOf(next.feature.getStructure());
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isAncestorOf(Feature next) {
		return feature.getStructure().isAncestorOf(next.feature.getStructure());
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isFirstChild(child.feature.getStructure());
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isFirstChild(Feature child) {
		return feature.getStructure().isFirstChild(child.feature.getStructure());
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().getChildrenCount();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public int getChildrenCount() {
		return feature.getStructure().getChildrenCount();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * new Feature(IFeature.getStructure().getFirstChild().getFeature());
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public Feature getFirstChild() {
		return new Feature(feature.getStructure().getFirstChild().getFeature());
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * new Feature(IFeature.getStructure().getLastChild().getFeature());
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public Feature getLastChild() {
		return new Feature(feature.getStructure().getLastChild().getFeature());
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getChildIndex(feature);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public int getChildIndex(Feature feature) {
		return feature.getChildIndex(feature);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isAbstract();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isAbstract() {
		return feature.getStructure().isAbstract();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isConcrete();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isConcrete() {
		return feature.getStructure().isConcrete();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().isANDPossible();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean isANDPossible() {
		return feature.getStructure().isANDPossible();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.fireEvent(event);
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void fire(PropertyChangeEvent event) {
		feature.fireEvent(event);
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * new Feature(feature.clone(feature.getFeatureModel(), feature.getStructure()));
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	@Override
	public Feature clone() {
		return new Feature(feature.clone(feature.getFeatureModel(), feature.getStructure()));
	}

	public Feature clone(IFeatureModel featureModel, boolean complete) {
		throw new UnsupportedOperationException("Not implemented yet"):
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().setAnd();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setAnd() {
		feature.getStructure().setAnd();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().setOr();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setOr() {
		feature.getStructure().setOr();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().setAlternative();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public void setAlternative() {
		feature.getStructure().setAlternative();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getStructure().hasHiddenParent();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public boolean hasHiddenParent() {
		return feature.getStructure().hasHiddenParent();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.toString()
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	@Override
	public String toString() {
		return feature.toString();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getProperty().getDisplayName();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public String getDisplayName() {
		return feature.getProperty().getDisplayName();
	}

	@Override
	public void propertyChange(PropertyChangeEvent event) {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Deprecated
	public String toString(boolean writeMarks) {
		if (writeMarks) {
			if (feature.getName().name.contains(" ") || Operator.isOperatorName(feature.getName())) {
				return "\"" + feature.getName() + "\"";
			}
			return feature.getName();
		} else {
			return toString();
		}
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getGraphicRepresenation().getColorList();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	public ColorList getColorList() {
		return feature.getGraphicRepresenation().getColorList();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.hashCode();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	@Override
	public int hashCode() {
		return feature.hashCode();
	}

	/**
	 * <b>This class and all it's methods are deprecated and should <i>only</i> be used for compatibility reasons</b>
	 * </br>Internally, the <code>de.ovgu.featureide.fm.core.Feature</code> class uses a delegiation to an underlying
	 * {@link IFeature IFeature interface}.<br/><br/>
	 * Instead of this method you should use<br/>
	 * <code>
	 * IFeature.getGraphicRepresenation().getItemType();
	 * </code>
	 * 
	 * @author Marcus Pinnecke
	 * @since 2.7.5 
	 */
	@Deprecated
	@Override
	public GraphicItem getItemType() {
		return feature.getGraphicRepresenation().getItemType();
	}
}
