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
package de.ovgu.featureide.fm.core.base;

import javax.annotation.Nonnull;

import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * The feature interface represents any class that acts in the sense of a <i>feature</i> in FeatureIDE. A feature contains both <ul> <li>certain fixed
 * properties (e.g., its name) which are available by the features implementation of {@link de.ovgu.featureide.fm.core.base.IFeatureProperty IFeatureProperty},
 * and</li> <li>custom properties which can be stored and received in a key-value store like fashion without the need of modifying existing code</li> </ul> Each
 * feature belongs to other features where statements between features form a <i>feature model</i>. Hence, a feature is related to a <i>structure</i> which
 * connects the feature to, e.g., it's <i>children</i>, or it's <i>parent</i> feature in terms of these statements. Any feature is highly related to it's name
 * and identified by it's internal <i>identifier</i>. The last both properties are mixed-in with the {@link IFeatureModelElement} interface. An instance of
 * <code>IFeature</code> intended to be instantiated by a {@link IFeatureModelFactory}. <br/> <br/> FeatureIDE provides an adapter implementation
 * {@link de.ovgu.featureide.fm.core.base.impl.AFeature AFeature} which is a abstract base class and which should be prefered as starting point for custom
 * implementations. This base class contains ready-to-use implementations for both <code>IFeature</code> and {@link IFeatureModelElement}. <br/> <br/>
 * <b>Example</b><br/> The following example demonstrate the creation of a new feature called <i>FeatureA</i> using FeatureIDE's default <code>IFeature</code>
 * implementation {@link de.ovgu.featureide.fm.core.base.impl.Feature Feature}, and the corresponding default factory
 * {@link de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory DefaultFeatureModelFactory} over the conviennent factory class
 * {@link FMFactoryManager}: <code> <pre> IFeatureModel model = FMFactoryManager.getFactory().createFeatureModel(); IFeature feature =
 * FMFactoryManager.getFactory().createFeature(model, "FeatureA"); </pre> </code> A unified handling of certain <code>IFeature</code> implementations (in terms
 * of conviennent methods) can be achieved with the use of {@link de.ovgu.featureide.fm.core.base.FeatureUtils FeatureUtils} helper class. <br/> <br/> <b>API
 * notes</b>: The classes internal structure has heavily changed compared to older FeatureIDE version. A bridge to the old-fashioned handling is available in
 * {@link de.ovgu.featureide.fm.core.base.FeatureUtils FeatureUtils} as static methods. <br/> <br/> <b>Notes on equals method</b>: Any implementation have to
 * provide a {@link Object#equals(Object)} implementation when the feature implementation should be fully useable in the FeatureIDE system (and therefore, have
 * to be an instance of {@link IFeatureModelElement}), which at least returns <b>true</b> when the internal identifier of two features are the same, and
 * otherwise <b>false</b>. <br/> <br/> <b>Compatibility Notes</b>: To provide compatibility to earlier versions of FeatureIDE, the <i>out-dated</i> class
 * {@link de.ovgu.featureide.fm.core.Feature Feature} also implements the <code>IFeature</code> interface. Developers should neither use nor extend this
 * obsolete class since it is deprecated and will be removed in one of the next versions.
 *
 * @see de.ovgu.featureide.fm.core.base.impl.AFeature Default implementation of <code>IFeature</code> (as starting point for custom implementations)
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
public interface IFeature extends IFeatureModelElement {

	/**
	 * Creates a new instance (new reference) of this feature with the same feature name and internal id, optionally change the features feature model and/or
	 * structure.
	 *
	 * @since 3.0
	 *
	 * @param newFeatureModel A new feature model in which the feature should be part of. If this parameter is <code>null</code>, the cloned feature's new
	 *        feature model have to be the originals feature's feature model.
	 * @param newStructure A new structure in which the feature should life. If this parameter is <code>null</code>, the cloned feature's new structure have to
	 *        be the originals feature's structure.
	 *
	 * @since 3.0
	 *
	 * @return New instance <code>f'</code> of this feature <code>f</code> such that <code>f != f'</code> but <code>f.equals(f')</code> holds.
	 */
	IFeature clone(IFeatureModel newFeatureModel, IFeatureStructure newStructure);

	/**
	 * Returns the feature's properties. These properties depend on the {@link IFeatureProperty} implementation, but contain at least getters and setters for
	 * <ul> <li>a custom-defined description of the feature</li> <li>a string-representation of the feature which is intended for display purposes</li>
	 * <li>information about the feature status (dead, false-optional,...)</li> <li>the state of the feature's selection in the GUI</li> </ul> For user-defined
	 * properties, the {@link IFeatureProperty} implementation must be changed, or the method {@link #getCustomProperties()} can be used.
	 *
	 * @since 3.0
	 *
	 * @return Implementation-specific feature properties.
	 */
	IFeatureProperty getProperty();

	/**
	 * Returns the feature's custom-defined properties. These properties can be get and set without changes to the code base, or the need for a custom
	 * {@link IFeatureProperty} implementation (see {@link #getProperty()}). Custom-Properties do map a Java primitive value to a string key and can stored to
	 * the file system.
	 *
	 * @since 3.0
	 *
	 * @return Implementation-independent custom feature properties.
	 */
	IPropertyContainer getCustomProperties();

	/**
	 * Returns the feature structure, in which this feature lives in. The structure gives information about (and setter to) the children and the parent of this
	 * feature, and statement-related properties such as if this feature is part of an alternative group, or if it is abstract or hidden. <br/> <br/>
	 * <b>Note</b>: The returned object have to be non-null.
	 *
	 * @since 3.0
	 *
	 * @return The features structure properties.
	 */
	@Nonnull
	IFeatureStructure getStructure();

	/**
	 * Creates the tooltip for the feature. Used to have the same tooltip in the different views that are used within the project. The tooltip created for the
	 * feature depents on the parameter objects given to it.
	 *
	 * @param objects Objects to determine which content should be generated.
	 * @return Tooltip content as string
	 */
	String createTooltip(Object... objects);

}
