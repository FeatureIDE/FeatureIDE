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
package de.ovgu.featureide.fm.core.base.impl;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.IPropertyContainer;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;

/**
 * FeatureIDE's default {@link IFeature} implementation as the starting point for user-defined implementations. <br/> <br/> This class implements the minimum
 * functionality required for a {@link IFeature} class and further functionality from {@link AFeatureModelElement}. The first provides getter and setter of the
 * feature's <i>properties</i>, <i>custom properties</i>, and the feature's <i>structure</i> (for more information, see {@link IFeature} documentation). The
 * second implements FeatureIDE's internal functionality to identify a given feature inside a feature model, and to provide event listening capabilities with
 * the listener/observer pattern. <br/> <br/> This class is intended to be a starting point for user-defined implementation, such that a subclass of
 * <code>AFeature</code> only have to provide an implementation of {@link IFeature#clone(IFeatureModel, IFeatureStructure)}. FeatureIDE provides a default
 * non-abstract implementation {@link de.ovgu.featureide.fm.core.base.impl.Feature Feature} which extends <code>AFeature</code> in this sense. <br/> <br/> An
 * instance of a subclass of <code>AFeature</code> is intended to be instantiated by a {@link IFeatureModelFactory}. <br/> <br/> <b>Example</b><br/> The
 * following example demonstrate the creation of a new feature called <i>FeatureA</i> using FeatureIDE's default <code>AFeature</code> implementation
 * {@link de.ovgu.featureide.fm.core.base.impl.Feature Feature}, and the corresponding default factory
 * {@link de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory DefaultFeatureModelFactory} over the conviennent factory class
 * {@link FMFactoryManager}. The instance is stored against the <code>IFeature</code> interface: <code> <pre> IFeatureModel model =
 * FMFactoryManager.getFactory().createFeatureModel(); IFeature feature = FMFactoryManager.getFactory().createFeature(model, "FeatureA"); </pre> </code> A
 * unified handling of certain <code>AFeature</code> (<code>IFeature</code>) implementations (in terms of conviennent methods) can be achieved with the use of
 * {@link de.ovgu.featureide.fm.core.base.FeatureUtils FeatureUtils} helper class. <br/> <br/> <b>Notes on equals method</b>: The <code>AFeature</code>
 * implementation inherits the {@link Object#equals(Object)} capability from {@link AFeatureModelElement}. The feature equality is defined as the equality of
 * the underlying internal identifiers per feature. <br/> <br/>
 *
 * @see de.ovgu.featureide.fm.core.base.IFeature Interface for feature in FeatureIDE (<code>IFeature</code>)
 *
 * @see IConstraint Interface for feature constraints (<code>IConstraint</code>)
 * @see IFeatureModel Interface for feature models (<code>IFeatureModel</code>)
 * @see IFeatureProperty Interface for feature properties (<code>IFeatureProperty</code>)
 * @see IFeatureStructure Interface for a feature's structure (<code>IFeatureStructure</code>)
 *
 * @see de.ovgu.featureide.fm.core.base.impl.AConstraint Default implementation for feature constraints (<code>AConstraint</code>)
 * @see de.ovgu.featureide.fm.core.base.impl.FeatureModel Default implementation for feature models (<code>FeatureModel</code>)
 * @see de.ovgu.featureide.fm.core.base.impl.FeatureProperty Default implementation for feature properties (<code>FeatureProperty</code>)
 * @see de.ovgu.featureide.fm.core.base.impl.FeatureStructure Default implementation for a feature's structure (<code>FeatureStructure</code>)
 *
 * @since 3.0
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public abstract class AFeature extends AFeatureModelElement implements IFeature {

	protected final IFeatureProperty property;
	protected final IFeatureStructure structure;
	protected final IPropertyContainer propertyContainer;

	/**
	 * <b>Copy constructor</b>. Constructs a new instance of <code>AFeature</code> given another feature <code>oldFeature</code>, a feature model
	 * <code>featureModel</code>, and a feature structure <code>newFeatureStructure</code> (for further information on feature model and structure, see
	 * {@link IFeature} and {@link IFeatureModel}). Moreover, the user-defined properties are copied. <br/> <br/> <b>Note</b>: The parameter
	 * <code>oldFeature</code> have to be non-null. The getter {@link AFeatureModelElement#getName()} of <code>oldFeature</code> (as an subclass of
	 * {@link AFeatureModelElement) can be <b>null</b>.
	 *
	 * @param oldFeature used to copy the original feature's identifier, and the original feature's name (if available)
	 * @param featureModel is used to set the new feature's feature model if <code>featureModel</code> is non-null. If <code>featureModel</code> is <b>null</b>,
	 *        a reference to the feature model of <code>oldFeature</code> will be used.
	 * @param newFeatrureStructure is used to set the new feature's feature structure if <code>newFeatrureStructure</code> is non-null. If
	 *        <code>newFeatrureStructure</code> is <b>null</b>, a reference to the feature structure <code>oldFeature</code> will be used.
	 *
	 * @since 3.0
	 */
	protected AFeature(AFeature oldFeature, IFeatureModel featureModel, IFeatureStructure newFeatrureStructure) {
		super(oldFeature, featureModel);

		property = oldFeature.property.clone(this);
		structure = newFeatrureStructure != null ? newFeatrureStructure : oldFeature.structure;
		propertyContainer = clonePropertyContainer(oldFeature);
		propertyContainer.setEntrySet(oldFeature.getCustomProperties().entrySet());
	}

	/**
	 * <b>Default constructor</b>. Constructs a new instance of <code>AFeature</code> with the name <code>name</code> in a given feature model
	 * <code>featureModel</code>. The parameter <code>featureModel</code> have to be non-null since features are identified by their internal numerical
	 * identifier and <code>featureModel</code> have to provide the next free identifier.
	 *
	 * @param featureModel in which the new instance feature should be part of
	 * @param name the name of the feature.
	 *
	 * @since 3.0
	 */
	public AFeature(IFeatureModel featureModel, String name) {
		super(featureModel);
		this.name = name;

		property = createProperty();
		structure = createStructure();
		propertyContainer = createPropertyContainer();
	}

	protected IPropertyContainer createPropertyContainer() {
		return new MapPropertyContainer();
	}

	protected IPropertyContainer clonePropertyContainer(AFeature other) {
		return new MapPropertyContainer(other.propertyContainer);
	}

	protected IFeatureProperty createProperty() {
		return new FeatureProperty(this);
	}

	protected IFeatureStructure createStructure() {
		return new FeatureStructure(this);
	}

	@Override
	public IFeatureProperty getProperty() {
		return property;
	}

	@Override
	public IFeatureStructure getStructure() {
		return structure;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public void setName(String name) {
		final String oldName = this.name;
		super.setName(name);
		fireEvent(new FeatureIDEEvent(this, EventType.FEATURE_NAME_CHANGED, oldName, name));
	}

	@Override
	public IPropertyContainer getCustomProperties() {
		return propertyContainer;
	}

	@Override
	public String toString() {
		return getName();
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
