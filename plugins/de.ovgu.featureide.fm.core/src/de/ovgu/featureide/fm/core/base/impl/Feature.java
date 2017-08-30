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

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.FeatureConnection;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Implementation of {@link AFeature} used as default implementation inside FeatureIDE.
 * <br/>
 * <br/>
 * This class implements the functionality required by {@link IFeature} and a {@link AFeatureModelElement}, specified in {@link AFeature}.
 * <br/>
 * <br/>
 * This class is intended to be the default implementation for regular use-cases of feature management. Further specialization for other use-cases is available
 * in the sub classes {@link ExtendedFeature} and inside {@link de.ovgu.featureide.fm.core.io.sxfm.SXFMReader SXFMReader}.
 * <br/>
 * <br/>
 * An instance of a <code>Feature</code> is intended to be instantiated by a {@link IFeatureModelFactory}.
 * <br/>
 * <br/>
 * <b>Example</b><br/>
 * The following example demonstrate the creation of a new feature called <i>FeatureA</i> using FeatureIDE's default <code>IFeature</code> (
 * <code>AFeature</code>) implementation
 * {@link de.ovgu.featureide.fm.core.base.impl.Feature Feature}, and the corresponding default factory
 * {@link de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory DefaultFeatureModelFactory} over the conviennent factory class
 * {@link FMFactoryManager}. The instance is stored against the <code>IFeature</code> interface:
 * <code>
 * <pre>
 * IFeatureModel model = FMFactoryManager.getFactory().createFeatureModel();
 * IFeature feature = FMFactoryManager.getFactory().createFeature(model, "FeatureA");
 * </pre>
 * </code>
 * A unified handling of certain <code>Feature</code> (<code>AFeature</code>, <code>IFeature</code>) implementations (in terms of conviennent methods) can be
 * achieved with the use of
 * {@link de.ovgu.featureide.fm.core.base.FeatureUtils FeatureUtils} helper class.
 *
 * @see de.ovgu.featureide.fm.core.base.AFeature Default implementation of the interface for feature in FeatureIDE (<code>AFeature</code>)
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
 * @author Thomas Thuem
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public class Feature extends AFeature {
	

	/**
	 * <b>Copy constructor</b>. Constructs a new instance of <code>Feature</code> given another feature <code>oldFeature</code>, a feature model
	 * <code>featureModel</code>, and a
	 * feature structure <code>newFeatureStructure</code> (for further information on feature model and structure, see {@link IFeature} and
	 * {@link IFeatureModel}). Moreover, the user-defined properties are copied.
	 * <br/>
	 * <br/>
	 * <b>Note</b>: The parameter <code>oldFeature</code> have to be non-null. The getter {@link AFeatureModelElement#getName()} of <code>oldFeature</code> (as
	 * an subclass of {@link AFeatureModelElement) can be <b>null</b>.
	 * 
	 * @param oldFeature used to copy the original feature's identifier, and the original feature's name (if available)
	 * @param featureModel is used to set the new feature's feature model if <code>featureModel</code> is non-null. If <code>featureModel</code> is <b>null</b>,
	 *            a
	 *            reference to the feature model of <code>oldFeature</code> will be used.
	 * @param newFeatrureStructure is used to set the new feature's feature structure if <code>newFeatrureStructure</code> is non-null. If
	 *            <code>newFeatrureStructure</code> is <b>null</b>, a reference to the feature structure <code>oldFeature</code> will be used.
	 * 
	 * @since 3.0
	 */
	
	protected Feature(Feature oldFeature, IFeatureModel featureModel, IFeatureStructure newFeatrureStructure) {
		super(oldFeature, featureModel, newFeatrureStructure);
	}

	/**
	 * <b>Default constructor</b>. Constructs a new instance of <code>AFeature</code> with the name <code>name</code> in a given feature model
	 * <code>featureModel</code>.
	 * The parameter <code>featureModel</code> have to be non-null since features are identified by their internal numerical identifier and
	 * <code>featureModel</code> have to provide the next free identifier.
	 * 
	 * @param featureModel in which the new instance feature should be part of
	 * @param name the name of the feature.
	 * 
	 * @since 3.0
	 */
	public Feature(IFeatureModel featureModel, String name) {
		super(featureModel, name);
	}
	

	private final LinkedList<FeatureConnection> sourceConnections = new LinkedList<FeatureConnection>();
	
	private LinkedList<PropertyChangeListener> listenerList = new LinkedList<PropertyChangeListener>();
	
	public void fire(PropertyChangeEvent event) {
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	@Override
	protected IFeatureProperty createProperty() {
		return new FeatureProperty(this);
	}

	@Override
	protected IFeatureStructure createStructure() {
		return new FeatureStructure(this);
	}

	@Override
	public IFeature clone(IFeatureModel newFeatureModel, IFeatureStructure newStructure) {
		return new Feature(this, newFeatureModel, newStructure);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.base.IFeature#getParent()
	 */
//	@Override

//	private IFeature parent;
	public IFeature feature;
	public IFeature getParent() {
//		return null;
//		return parent;
		return FeatureUtils.getParent(feature);
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.base.IFeature#isConcrete()
	 */
//	@Override
//	private boolean concret;
	public boolean isConcrete() {
//		return false;
//		return concret;
		return FeatureUtils.isConcrete(feature);
	}
	
	public String getDisplayName() {
		return FeatureUtils.getDisplayName(feature);
	}

}
