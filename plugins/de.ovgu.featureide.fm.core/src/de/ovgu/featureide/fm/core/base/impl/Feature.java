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

import static de.ovgu.featureide.fm.core.localization.StringTable.CONCRETE;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_MODEL_IS_VOID;
import static de.ovgu.featureide.fm.core.localization.StringTable.INHERITED_HIDDEN;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_DEAD;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_FALSE_OPTIONAL;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_HIDDEN_AND_INDETERMINATE;
import static de.ovgu.featureide.fm.core.localization.StringTable.ROOT;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureProperty;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Implementation of {@link AFeature} used as default implementation inside FeatureIDE. <br/> <br/> This class implements the functionality required by
 * {@link IFeature} and a {@link AFeatureModelElement}, specified in {@link AFeature}. <br/> <br/> This class is intended to be the default implementation for
 * regular use-cases of feature management. Further specialization for other use-cases is available in the sub classes {@link ExtendedFeature} and inside
 * {@link de.ovgu.featureide.fm.core.io.sxfm.SXFMReader SXFMReader}. <br/> <br/> An instance of a <code>Feature</code> is intended to be instantiated by a
 * {@link IFeatureModelFactory}. <br/> <br/> <b>Example</b><br/> The following example demonstrate the creation of a new feature called <i>FeatureA</i> using
 * FeatureIDE's default <code>IFeature</code> ( <code>AFeature</code>) implementation {@link de.ovgu.featureide.fm.core.base.impl.Feature Feature}, and the
 * corresponding default factory {@link de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory DefaultFeatureModelFactory} over the conviennent factory
 * class {@link FMFactoryManager}. The instance is stored against the <code>IFeature</code> interface: <code> <pre> IFeatureModel model =
 * FMFactoryManager.getFactory().createFeatureModel(); IFeature feature = FMFactoryManager.getFactory().createFeature(model, "FeatureA"); </pre> </code> A
 * unified handling of certain <code>Feature</code> (<code>AFeature</code>, <code>IFeature</code>) implementations (in terms of conviennent methods) can be
 * achieved with the use of {@link de.ovgu.featureide.fm.core.base.FeatureUtils FeatureUtils} helper class.
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

	private static String ABSTRACT = " Abstract";
	private static String HIDDEN = " hidden";
	private static String HIDDEN_PARENT = INHERITED_HIDDEN;
	private static String DEAD = IS_DEAD;
	private static String FEATURE = " feature ";
	private static String FALSE_OPTIONAL = IS_FALSE_OPTIONAL;
	private static String INDETERMINATE_HIDDEN = IS_HIDDEN_AND_INDETERMINATE;
	private static String VOID = FEATURE_MODEL_IS_VOID;

	/**
	 * <b>Copy constructor</b>. Constructs a new instance of <code>Feature</code> given another feature <code>oldFeature</code>, a feature model
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
	protected Feature(Feature oldFeature, IFeatureModel featureModel, IFeatureStructure newFeatrureStructure) {
		super(oldFeature, featureModel, newFeatrureStructure);
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
	public Feature(IFeatureModel featureModel, String name) {
		super(featureModel, name);
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

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.base.impl.AFeature#createTooltip(java.lang.Object[])
	 */
	@Override
	public String createTooltip(Object... objects) {
		final StringBuilder toolTip = new StringBuilder();
		final FeatureModelAnalyzer analyser = getFeatureModel().getAnalyser();

		toolTip.append(getStructure().isConcrete() ? CONCRETE : ABSTRACT);

		if (getStructure().hasHiddenParent()) {
			toolTip.append(getStructure().isHidden() ? HIDDEN : HIDDEN_PARENT);
		}

		toolTip.append(getStructure().isRoot() ? ROOT : FEATURE);

		switch (getProperty().getFeatureStatus()) {
		case DEAD:
			toolTip.append(DEAD);
			break;
		case FALSE_OPTIONAL:
			toolTip.append(FALSE_OPTIONAL);
			break;
		case INDETERMINATE_HIDDEN:
			toolTip.append(INDETERMINATE_HIDDEN);
			break;
		default:
			break;
		}

		if (!analyser.valid()) {
			toolTip.setLength(0);
			toolTip.trimToSize();
			toolTip.append(VOID);
		}

		final String description = getProperty().getDescription();
		if ((description != null) && !description.trim().isEmpty()) {
			toolTip.append("\n\nDescription:\n");
			toolTip.append(description);
		}

		final String contraints = FeatureUtils.getRelevantConstraintsString(this);
		if (!contraints.isEmpty()) {
			toolTip.append("\n\nConstraints:\n");
			toolTip.append(contraints);
		}

		return toolTip.toString();
	}
}
