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
package de.ovgu.featureide.fm.core.base;

import static de.ovgu.featureide.fm.core.functional.Functional.filter;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.filter.ConcreteFeatureFilter;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.functional.Functional.IFunction;

/**
 * @author Marcus Pinnecke
 */
public abstract class FeatureUtils {
	
	public static final ConcreteFeatureFilter CONCRETE_FEATURE_FILTER = new ConcreteFeatureFilter();
	
	public static final IFunction<IFeature, String> GET_FEATURE_NAME = new IFunction<IFeature, String>() {
		
		@Override
		public String invoke(IFeature t) {
			return t.getName();
		}
	};
	
	public static final IFunction<IFeatureStructure, IFeature> STRUCTURE_TO_FEATURE = new IFunction<IFeatureStructure, IFeature>() {
		
		@Override
		public IFeature invoke(IFeatureStructure t) {
			return t.getFeature();
		}
	};
	
	public static final IFunction<IFeature, IFeatureStructure> FEATURE_TO_STRUCTURE = new IFunction<IFeature, IFeatureStructure>() {
		
		@Override
		public IFeatureStructure invoke(IFeature t) {
			return t.getStructure();
		}
	};
	
	/**
	 * Extracts all concrete features from an object that yields features. Basically, an invocation of this method on <b>features</b> will return an iterable object that
	 * yields a feature <i>f</i> from <b>features</b> if and only if <i>f</i> is concrete. Since the implementation based on iterators, it is a lazy filtering without
	 * modification of <b>features</b>. 
	 * 
	 * <br/><br/>The extraction is done via {@link de.ovgu.featureide.fm.core.functional.Functional#filter(Iterable, de.ovgu.featureide.fm.core.filter.base.IFilter)}
	 * 
	 * @since 2.7.5
	 * @param features An iterable object providing features
	 * @author Marcus Pinnecke
	 * @return An iterable object that yields all concrete features of <b>features</b>
	 */
	public static Iterable<IFeature> extractConcreteFeatures(final Iterable<IFeature> features) {
		return filter(features, CONCRETE_FEATURE_FILTER);
	}
	
	/**
	 * Extracts all concrete features from a feature model by calling {@link #extractConcreteFeatures(Iterable)} on <code>model.getFeatures()</code>.
	 * 
	 * @since 2.7.5
	 * @param model A feature model
	 * @author Marcus Pinnecke
	 * @return An iterable object that yields all concrete features of <b>features</b>
	 */
	public static Iterable<IFeature> extractConcreteFeatures(final IFeatureModel model) {
		return extractConcreteFeatures(model.getFeatures());
	}
	
	/**
	 * Extracts all concrete features from a feature model as a list of strings by calling 
	 * {@link de.ovgu.featureide.fm.core.functional.Functional#mapToStringList(Iterable)} on the result of {@link #extractConcreteFeatures(IFeatureModel)}
 	 * using <code>model.getFeatures()</code>.
	 * 
	 * @since 2.7.5
	 * @param model A feature model
	 * @author Marcus Pinnecke
	 * @return A list of strings that contains the feature names of all concrete features of <b>features</b>
	 */
	public static List<String> extractConcreteFeaturesAsStringList(IFeatureModel model) {
		return Functional.mapToStringList(FeatureUtils.extractConcreteFeatures(model.getFeatures()));
	}

	public static Iterable<String> extractFeatureNames(Collection<IFeature> features) {
		return Functional.map(features, GET_FEATURE_NAME);
	}

	public static List<IFeature> convertToFeatureList(List<IFeatureStructure> list) {
		return Functional.toList(Functional.map(list, STRUCTURE_TO_FEATURE));
	}

	public static List<IFeatureStructure> convertToFeatureStructureList(List<IFeature> list) {
		return Functional.toList(Functional.map(list, FEATURE_TO_STRUCTURE));
	}

}
