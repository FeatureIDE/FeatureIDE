/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import java.io.File;
import java.util.Collection;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.IFMComposerExtension;
import de.ovgu.featureide.fm.core.RenamingsManager;
import de.ovgu.featureide.fm.core.base.event.IEventManager;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * The feature model interface represents any class that acts in the sense of a <i>feature model</i> in FeatureIDE. 
 * <br/><br/>
 * A feature model contains of a modifiable collection of 
 * <ul>
 * <li>{@link de.ovgu.featureide.fm.core.base.IFeature Features}, and</li>
 * <li>{@link de.ovgu.featureide.fm.core.base.IConstraint Constraints of features}</li>
 * </ul>
 * <br/>
 * Each <i>feature</i> in a feature model has a unique identifier and is related to other features over some expressions and relations which
 * forms the feature model (such as parent-children relation with implication expression from one feature to another). Additional to the 
 * structure of features (see {@link de.ovgu.featureide.fm.core.base.IFeature} and {@link de.ovgu.featureide.fm.core.base.IFeatureStructure} for more details) 
 * inside the feature models tree, features relationships can be further expressed using <i>constraints</i>. While the feature structure is bound to the 
 * actual feature model tree, constraints can be state restrictions and relations to arbitrary features inside the feature model. 
 * <br/><br/>
 * Features inside a feature model can by analyzed in order to determine feature properties which are implicated by the structure, the statements, and the constraints.
 * As a result of such an analysis, a set of <i>dead features</i> can be found for instance. For more information about analysis, see {@link de.ovgu.featureide.fm.core.FeatureModelAnalyzer FeatureModelAnalyzer}.
 * <br/><br/>
 * Additional to the collection mentioned above, the feature model contains properties to express
 * <ul>
 * 	<li>Annotations</li>
 * 	<li>Comments</li>
 *  <li>Feature Orders</li>
 * </ul>
 * <br/>
 * A feature model is moreover related to it's project, such that the <i>project's name</i> can be received, the related composer extension can be received, as well as certain 
 * event handling logic (such as model data change event handling) can be made.
 * <br/><br/>
 * Any feature model is intended to be instantiated by a corresponding factory, the implementation-specific {@link IFeatureModelFactory feature model factory}. 
 * <br/><br/>
 * FeatureIDE provides a default implementation {@link de.ovgu.featureide.fm.core.base.impl.FeatureModel FeatureModel} which is used for default use-cases and can be customized via inheritance of {@link de.ovgu.featureide.fm.core.base.impl.FeatureModel feature model} and a user-defined {@IFeatureModelFactory feature model factory}. 
 * Internally, a feature model is represented by an unique numeric identifier, which should be considered in the related {@link IFeatureModelFactory feature model factory} in order to avoid confusion with other models.
 * <br/><br/>
 * <b>Example</b><br/>
 * The following example demonstrate the creation of a new feature model using FeatureIDE's default <code>FeatureModel</code> implementation
 * {@link de.ovgu.featureide.fm.core.base.impl.FeatureModel FeatureModel}, and the corresponding default factory
 * {@link de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory DefaultFeatureModelFactory} over the conviennent factory class
 * {@link FMFactoryManager}:
 * <code>
 * <pre>
 * IFeatureModel model = FMFactoryManager.getFactory().createFeatureModel();
 * </pre>
 * </code>
 * A unified handling of certain <code>IFeature</code>, and <code>IFeatureModel</code> implementations (in terms of conviennent methods) can be achieved with the use of
 * {@link de.ovgu.featureide.fm.core.base.FeatureUtils FeatureUtils} helper class.
 * <br/>
 * <br/>
 * <b>API notes</b>: The classes internal structure has heavily changed compared to older FeatureIDE version. A bridge to the old-fashioned handling is available in {@link de.ovgu.featureide.fm.core.base.FeatureUtils FeatureUtils} as static methods.
 * <br/>
 * <br/>
 * <b>Notes on thread safeness</b>: At least the management of <code>IFeature</code> identifiers (e.g., getting the next free id) have to be thread safe. 
 * <br/>
 * <br/>
 * <b>Compatibility Notes</b>: To provide compatibility to earlier versions of FeatureIDE, the <i>out-dated</i> class {@link de.ovgu.featureide.fm.core.FeatureModel
 * FeatureModel} is now a wrapper to an <code>IFeatureModel</code> instance (but incompatible to it) and make use of convert-functionalities inside
 *  {@link de.ovgu.featureide.fm.core.base.FeatureUtils FeatureUtils}.
 * 
 * @see de.ovgu.featureide.fm.core.base.impl.FeatureModel Default implementation of <code>IFeatureModel</code> (as starting point for custom implementations)
 * 
 * @see IFeature Interface for features (<code>IFeature</code>)
 * @see IConstraint Interface for feature constraints (<code>IConstraint</code>)
 * @see IFeatureProperty Interface for feature properties (<code>IFeatureProperty</code>)
 * @see IFeatureStructure Interface for a feature's structure  (<code>IFeatureStructure</code>)
 * 
 * @see de.ovgu.featureide.fm.core.base.impl.Feature Default implementation for features (<code>Feature</code>)
 * @see de.ovgu.featureide.fm.core.base.impl.AConstraint Default implementation for feature constraints (<code>AConstraint</code>)
 * @see de.ovgu.featureide.fm.core.base.impl.FeatureProperty Default implementation for feature properties (<code>FeatureProperty</code>)
 * @see de.ovgu.featureide.fm.core.base.impl.FeatureStructure Default implementation for a feature's structure (<code>FeatureStructure</code>)
 * 
 * @since 3.0
 * 
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public interface IFeatureModel extends Cloneable, IEventManager {

	long getId();

	void addConstraint(IConstraint constraint);

	void addConstraint(IConstraint constraint, int index);

	boolean addFeature(IFeature feature);

	IFeatureModel clone(IFeature newRoot);

	void createDefaultValues(CharSequence projectName);

	boolean deleteFeature(IFeature feature);

	void deleteFeatureFromTable(IFeature feature);

	FeatureModelAnalyzer getAnalyser();

	int getConstraintCount();

	int getConstraintIndex(IConstraint constraint);

	List<IConstraint> getConstraints();

	IFeature getFeature(CharSequence name);

	Collection<String> getFeatureOrderList();

	Iterable<IFeature> getFeatures();

	IFMComposerExtension getFMComposerExtension();

	FMComposerManager getFMComposerManager(final IProject project);

	int getNumberOfFeatures();

	IFeatureModelProperty getProperty();

	RenamingsManager getRenamingsManager();

	IFeatureModelStructure getStructure();

	void handleModelDataChanged();

	void handleModelDataLoaded();

	IFMComposerExtension initFMComposerExtension(final IProject project);

	boolean isFeatureOrderUserDefined();

	void removeConstraint(IConstraint constraint);

	void removeConstraint(int index);

	void replaceConstraint(IConstraint constraint, int index);

	void reset();

	void setConstraints(final Iterable<IConstraint> constraints);

	void setFeatureOrderList(final List<String> featureOrderList);

	void setFeatureOrderUserDefined(boolean featureOrderUserDefined);

	void setFeatureTable(final Hashtable<String, IFeature> featureTable);

	Map<String, IFeature> getFeatureTable(); // Added, Marcus Pinnecke 31.08.15

	IFeatureModel clone();

	Object getUndoContext();

	void setUndoContext(Object undoContext);

	void setFeatureOrderListItem(int i, String newName);

	void setSourceFile(File file);

	File getSourceFile();

	long getNextElementId();

	void setConstraint(int index, Constraint constraint);

}
