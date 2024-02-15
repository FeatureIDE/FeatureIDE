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
package de.ovgu.featureide.fm.core;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.AllConfigurationGenerator;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.SliceFeatureModel;

/**
 * Test for slicing a feature model.
 *
 * @author Sebastian Krieter
 */
public class TFeatureModelSlicing {

	@Test
	public final void silcingWorksforCar() {
		testModel("car.xml");
	}

	@Test
	public final void silcingWorksforGPL() {
		testModel("gpl_medium_model.xml");
	}

	private void testModel(String modelFileName) {
		final IFeatureModel featureModel = Commons.loadTestFeatureModelFromFile(modelFileName);
		// There is no loop here on purposes,
		// it makes tracing easier in case of a test failure
		sliceModel(featureModel, new Random(0).nextLong());
		sliceModel(featureModel, new Random(1).nextLong());
		sliceModel(featureModel, new Random(2).nextLong());
		sliceModel(featureModel, new Random(3).nextLong());
		sliceModel(featureModel, new Random(4).nextLong());
		sliceModel(featureModel, new Random(5).nextLong());
		sliceModel(featureModel, new Random(6).nextLong());
		sliceModel(featureModel, new Random(7).nextLong());
		sliceModel(featureModel, new Random(8).nextLong());
		sliceModel(featureModel, new Random(9).nextLong());
	}

	private void sliceModel(final IFeatureModel featureModel, long randomSeed) {
		final List<String> featureNames = featureModel.getFeatures().stream().map(IFeature::getName).collect(Collectors.toList());
		Collections.shuffle(featureNames.subList(1, featureNames.size()), new Random(randomSeed));
		final int removeIndex = featureNames.size() / 2;
		final List<String> featuresToKeep = featureNames.subList(0, removeIndex);
		final List<String> featuresToRemove = featureNames.subList(removeIndex, featureNames.size());

		final IFeatureModel slicedModel = LongRunningWrapper.runMethod(new SliceFeatureModel(featureModel, featuresToKeep, true));

		final FeatureModelFormula orgFormula = new FeatureModelFormula(featureModel);
		final FeatureModelFormula slicedFormula = new FeatureModelFormula(slicedModel);

		final Set<HashSet<String>> orgSolutionSet = LongRunningWrapper.runMethod(new AllConfigurationGenerator(orgFormula.getCNF())) //
				.stream() //
				.map(orgFormula.getVariables()::convertToString) //
				.map(HashSet::new) //
				.peek(s -> s.removeAll(featuresToRemove)) //
				.collect(Collectors.toSet());
		final Set<HashSet<String>> slicedSolutionSet = LongRunningWrapper.runMethod(new AllConfigurationGenerator(slicedFormula.getCNF())) //
				.stream() //
				.map(slicedFormula.getVariables()::convertToString) //
				.map(HashSet::new) //
				.collect(Collectors.toSet());

		assertEquals(orgSolutionSet, slicedSolutionSet);

		addFeature(slicedModel, FMFactoryManager.getInstance().getFactory(featureModel), "NewFeatureFromOldFactory", featuresToRemove.size());
		addFeature(slicedModel, FMFactoryManager.getInstance().getFactory(slicedModel), "NewFeatureFromNewFactory", featuresToRemove.size());

		final Map<IFeatureModelElement, IFeatureModelElement> elementSet = new HashMap<>();
		checkForDuplicateElements(elementSet, slicedModel.getFeatures());
		checkForDuplicateElements(elementSet, slicedModel.getConstraints());
	}

	private void addFeature(final IFeatureModel model, IFeatureModelFactory factory, String namePrefix, int count) {
		for (int i = 0; i < count; i++) {
			model.addFeature(factory.createFeature(model, namePrefix + i));
		}
	}

	private void checkForDuplicateElements(final Map<IFeatureModelElement, IFeatureModelElement> elementSet,
			Collection<? extends IFeatureModelElement> elements) {
		for (final IFeatureModelElement element : elements) {
			final IFeatureModelElement mappedElement = elementSet.get(element);
			if (mappedElement == null) {
				elementSet.put(element, element);
			} else {
				fail(String.format("Element %s already contained in feature model as %s.", element, mappedElement));
			}
		}
	}

}
