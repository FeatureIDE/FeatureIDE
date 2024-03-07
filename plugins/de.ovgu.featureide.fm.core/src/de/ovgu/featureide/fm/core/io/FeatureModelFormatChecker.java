/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.IPropertyContainer.Entry;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * Checks incompatibilities of Feature Model Formats
 *
 * @author Andreas Gerasimow
 */
public class FeatureModelFormatChecker {

	private final static String IMPORT_ONLY = "This format may only be imported.";
	private final static String EXPORT_ONLY = "This format may only be exported.";
	private final static String COLORS_NOT_EXPORTED = "Colors can't be exported as they are not part of the feature model file.";
	private final static String IS_MISSING = "is missing";
	private final static String WILL_BE_DIFFERENT = "will be different.";

	public static ProblemList checkFormat(IPersistentFormat<IFeatureModel> format, IFeatureModel model) {
		final ProblemList problemList = new ProblemList();
		final boolean supportsRead = format.supportsRead();
		final boolean supportsWrite = format.supportsWrite();

		if (supportsRead && supportsWrite) {
			final String stringModel = format.write(model);
			try {
				final IFeatureModel model2 = FMFactoryManager.getInstance().getFactory(format).create();
				final ProblemList problemList2 = format.read(model2, stringModel);
				problemList.addAll(checkModelProperties(model, model2));
				problemList.addAll(checkFeatures(model, model2));
				problemList.addAll(checkTreeStructure(model, model2));
				problemList.addAll(checkConstraints(model, model2));
				problemList.addAll(checkColors(model, model2));
				problemList.addAll(problemList2);
			} catch (final NoSuchExtensionException e) {}
		} else if (supportsRead) {
			problemList.add(new Problem(IMPORT_ONLY, 0));
		} else if (supportsWrite) {
			problemList.add(new Problem(EXPORT_ONLY, 0));
			problemList.add(new Problem(COLORS_NOT_EXPORTED, 0));
		}

		model.getProperty().getProperties();
		model.getStructure();
		return problemList;
	}

	private static ProblemList checkModelProperties(IFeatureModel oldModel, IFeatureModel newModel) {
		final ProblemList problemList = new ProblemList();
		final List<Entry> oldProperties = new ArrayList<>(oldModel.getProperty().getProperties());
		final Set<Entry> newProperties = new LinkedHashSet<>(newModel.getProperty().getProperties());

		final boolean sameSize = oldProperties.size() == newProperties.size();

		oldProperties.forEach((oldProperty) -> {
			if (!newProperties.contains(oldProperty)) {
				problemList.add(new Problem("The property with type \"" + oldProperty.getType() + "\" and key \"" + oldProperty.getKey() + "\" "
					+ (sameSize ? WILL_BE_DIFFERENT : IS_MISSING), 0));
			}
		});

		return problemList;
	}

	private static ProblemList checkFeatures(IFeatureModel oldModel, IFeatureModel newModel) {
		final ProblemList problemList = new ProblemList();

		final List<IFeature> oldFeatures = new ArrayList<>(oldModel.getFeatures());
		final Map<Long, IFeature> newFeatures = new HashMap<>();
		newModel.getFeatures().forEach((newFeature) -> newFeatures.put(newFeature.getInternalId(), newFeature));

		oldFeatures.forEach((oldFeature) -> {
			final IFeature newFeature = newFeatures.get(oldFeature.getInternalId());

			if (newFeature == null) {

				problemList.add(new Problem(
						"The feature with id " + " \"" + oldFeature.getInternalId() + "\" and name \"" + oldFeature.getName() + "\" is missing.", 0));
			} else {
				// check feature structure
				final IFeatureStructure oldStructure = oldFeature.getStructure();
				final IFeatureStructure newStructure = newFeature.getStructure();

				// abstract / mandatory / hidden
				if (oldStructure.isAbstract() != newStructure.isAbstract()) {
					if (oldStructure.isAbstract()) {
						problemList.add(new Problem(
								"The feature with id \"" + oldFeature.getInternalId() + "\" and name \"" + oldFeature.getName() + "\" will not be abstract.",
								0));
					} else {
						problemList.add(new Problem(
								"The feature with id \"" + oldFeature.getInternalId() + "\" and name \"" + oldFeature.getName() + "\" be changed to abstract.",
								0));
					}
				}
				if (oldStructure.isMandatory() != newStructure.isMandatory()) {
					if (oldStructure.isMandatory()) {
						problemList.add(new Problem(
								"The feature with id \"" + oldFeature.getInternalId() + "\" and name \"" + oldFeature.getName() + "\" will not be mandatory.",
								0));
					} else {
						problemList.add(new Problem(
								"The feature with id \"" + oldFeature.getInternalId() + "\" and name \"" + oldFeature.getName() + "\" be changed to mandatory.",
								0));
					}
				}
				if (oldStructure.isHidden() != newStructure.isHidden()) {
					if (oldStructure.isHidden()) {
						problemList.add(new Problem(
								"The feature with id \"" + oldFeature.getInternalId() + "\" and name \"" + oldFeature.getName() + "\" will not be hidden.", 0));
					} else {
						problemList.add(new Problem(
								"The feature with id \"" + oldFeature.getInternalId() + "\" and name \"" + oldFeature.getName() + "\" be changed to hidden.",
								0));
					}
				}
				// relationships
				if (oldStructure.isAnd() != newStructure.isAnd()) {
					if (oldStructure.isAnd()) {
						problemList.add(new Problem("The feature with id " + " \"" + oldFeature.getInternalId() + "\" and name \"" + oldFeature.getName()
							+ "\" will not have \"and\" relationships.", 0));
					} else {
						problemList.add(new Problem("The relationships of the feature with id " + " \"" + oldFeature.getInternalId() + "\" and name \""
							+ oldFeature.getName() + "\" be changed to \"and\".", 0));
					}
				}
				if (oldStructure.isOr() != newStructure.isOr()) {
					if (oldStructure.isOr()) {
						problemList.add(new Problem("The feature with id " + " \"" + oldFeature.getInternalId() + "\" and name \"" + oldFeature.getName()
							+ "\" will not have \"or\" relationships.", 0));
					} else {
						problemList.add(new Problem("The relationships of the feature with id " + " \"" + oldFeature.getInternalId() + "\" and name \""
							+ oldFeature.getName() + "\" be changed to \"or\".", 0));
					}
				}
				if (oldStructure.isAlternative() != newStructure.isAlternative()) {
					if (oldStructure.isAlternative()) {
						problemList.add(new Problem("The feature with id " + " \"" + oldFeature.getInternalId() + "\" and name \"" + oldFeature.getName()
							+ "\" will not have \"alternative\" relationships.", 0));
					} else {
						problemList.add(new Problem("The relationships of the feature with id " + " \"" + oldFeature.getInternalId() + "\" and name \""
							+ oldFeature.getName() + "\" be changed to \"alternative\".", 0));
					}
				}
			}
		});

		return problemList;
	}

	private static ProblemList checkTreeStructure(IFeatureModel oldModel, IFeatureModel newModel) {
		final ProblemList problemList = new ProblemList();

		final List<IFeature> oldFeatures = new ArrayList<>(oldModel.getFeatures());
		final Map<Long, IFeature> newFeatures = new HashMap<>();
		newModel.getFeatures().forEach((newFeature) -> newFeatures.put(newFeature.getInternalId(), newFeature));

		oldFeatures.forEach((oldParentFeature) -> {
			oldParentFeature.getStructure().getChildren().forEach((oldChildFeature) -> {
				final IFeature newChildFeature = newFeatures.get(oldChildFeature.getFeature().getInternalId());
				if (newChildFeature != null) {
					final IFeature newParentFeature = newChildFeature.getStructure().getParent().getFeature();
					if (newParentFeature.getInternalId() != oldParentFeature.getInternalId()) {
						problemList.add(new Problem("The feature with id " + " \"" + oldChildFeature.getFeature().getInternalId() + "\" and name \""
							+ oldChildFeature.getFeature().getName() + "\" will have a different parent.", 0));
					}
				}
			});
		});

		return problemList;
	}

	private static ProblemList checkConstraints(IFeatureModel oldModel, IFeatureModel newModel) {
		final ProblemList problemList = new ProblemList();
		final List<IConstraint> oldConstraints = oldModel.getConstraints();
		final Set<String> newConstraints = newModel.getConstraints().stream().map(Object::toString).collect(Collectors.toSet());

		final boolean sameSize = oldConstraints.size() == newConstraints.size();

		oldConstraints.forEach((oldConstraint) -> {
			if (!newConstraints.contains(oldConstraint.toString())) {
				problemList.add(new Problem("The constraint \"" + oldConstraint.toString() + "\" " + (sameSize ? WILL_BE_DIFFERENT : IS_MISSING), 0));
			}
		});

		return problemList;
	}

	private static ProblemList checkColors(IFeatureModel oldModel, IFeatureModel newModel) {
		return new ProblemList(List.of(new Problem(COLORS_NOT_EXPORTED, 0)));
	}
}
