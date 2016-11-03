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
package de.ovgu.featureide.fm.core.base.impl;

import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID;
import static de.ovgu.featureide.fm.core.localization.StringTable.VALID;
import static de.ovgu.featureide.fm.core.localization.StringTable.VELVET_FEATUREMODEL_IMPORTED;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import javax.annotation.CheckForNull;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.constraint.Equation;
import de.ovgu.featureide.fm.core.constraint.FeatureAttributeMap;
import de.ovgu.featureide.fm.core.constraint.analysis.ExtendedFeatureModelAnalyzer;

/**
 * Adds attributes and attribute constraints to a feature model.
 * 
 * @author Sebastian Krieter
 * @author Matthias Strauss
 */
public class ExtendedFeatureModel extends FeatureModel {

	public static class UsedModel {
		private final String modelName;
		private final String varName;
		private final int type;

		private String prefix;

		public UsedModel(UsedModel usedModel, String parentName) {
			this.modelName = usedModel.modelName;
			this.varName = parentName + usedModel.varName;
			this.type = usedModel.type;
		}

		public UsedModel(String modelName, String varName, int type) {
			this.modelName = modelName;
			this.varName = varName;
			this.type = type;
		}

		public String getModelName() {
			return modelName;
		}

		public String getVarName() {
			return varName;
		}

		public int getType() {
			return type;
		}

		public String getPrefix() {
			return prefix;
		}

		public void setPrefix(String prefix) {
			this.prefix = prefix;
		}

		@Override
		public String toString() {
			return modelName + " " + varName;
		}
	}

	protected final List<String> imports = new LinkedList<String>();

	protected final FeatureAttributeMap<Integer> integerAttributes = new FeatureAttributeMap<Integer>();
	protected final FeatureAttributeMap<Boolean> booleanAttributes = new FeatureAttributeMap<Boolean>();
	protected final FeatureAttributeMap<String> stringAttributes = new FeatureAttributeMap<String>();
	protected final LinkedList<Equation> attributeConstraints = new LinkedList<Equation>();

	protected final Map<String, UsedModel> usedModels = new HashMap<String, UsedModel>();
	protected final List<IConstraint> ownConstraints = new LinkedList<IConstraint>();

	protected IFeatureModel mappingModel = null;

	private boolean isInterface = false;

	public ExtendedFeatureModel(String factoryID) {
		super(factoryID);
	}

	public List<String> getImports() {
		return imports;
	}

	public void addImport(String imp) {
		imports.add(imp.replace(".", "\\"));
	}

	@Override
	protected FeatureModelAnalyzer createAnalyser() {
		return new ExtendedFeatureModelAnalyzer(this);
	}

	public void addAttribute(final String featureName, final String attributeName, final Boolean value) {
		this.booleanAttributes.setAttribute(featureName, attributeName, value);
	}

	public void addAttribute(final String featureName, final String attributeName, final Integer value) {
		this.integerAttributes.setAttribute(featureName, attributeName, value);
	}

	public void addAttribute(final String featureName, final String attributeName, final String value) {
		this.stringAttributes.setAttribute(featureName, attributeName, value);
	}

	public void addAttributeConstraint(final Equation constraint) {
		this.attributeConstraints.add(constraint);
	}

	/**
	 * Adds a parameter to the available parameters of the model
	 * 
	 * @param varType
	 *            the name of the interface that shall be bound to the variable
	 * @param varName
	 *            the name of the variable an interface shall be bound to
	 * @return true if the parameter could be added to the parameters. False if
	 *         the variable name was already bound to another interface.
	 */
	public boolean addInterface(final String varType, final String varName) {
		return addModel(varType, varName, ExtendedFeature.TYPE_INTERFACE);
	}

	public boolean addInstance(final String varType, final String varName) {
		return addModel(varType, varName, ExtendedFeature.TYPE_INSTANCE);
	}

	public boolean addInheritance(final String varType, final String varName) {
		return addModel(varType, varName, ExtendedFeature.TYPE_INHERITED);
	}

	public boolean addExternalModel(final UsedModel model) {
		if (usedModels.containsKey(model.varName)) {
			return false;
		} else {
			usedModels.put(model.varName, model);
			return true;
		}
	}

	private boolean addModel(final String varType, final String varName, int modelType) {
		if (usedModels.containsKey(varName)) {
			return false;
		} else {
			usedModels.put(varName, new UsedModel(varType, varName, modelType));
			return true;
		}
	}

	public UsedModel getExternalModel(String varName) {
		return usedModels.get(varName);
	}

	public LinkedList<Equation> getAttributConstraints() {
		return this.attributeConstraints;
	}

	public FeatureAttributeMap<Boolean> getBooleanAttributes() {
		return this.booleanAttributes;
	}

	public FeatureAttributeMap<Integer> getIntegerAttributes() {
		return this.integerAttributes;
	}

	public FeatureAttributeMap<String> getStringAttributes() {
		return this.stringAttributes;
	}

	public boolean isMultiProductLineModel() {
		return !usedModels.isEmpty();
	}

	/**
	 * Check if the feature model contains instance features.
	 * 
	 * @return true if imported features exists
	 */
	public boolean hasInstance() {
		for (IFeature feature : featureTable.values()) {
			if (feature instanceof ExtendedFeature && ((ExtendedFeature) feature).isInstance()) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Check if the feature model contains inherited features.
	 * 
	 * @return true if inherited features exists
	 */
	public boolean hasInherited() {
		for (IFeature feature : featureTable.values()) {
			if (feature instanceof ExtendedFeature && ((ExtendedFeature) feature).isInherited()) {
				return true;
			}
		}
		return false;
	}

	public boolean hasInterface() {
		for (IFeature feature : featureTable.values()) {
			if (feature instanceof ExtendedFeature && ((ExtendedFeature) feature).isInterface()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public void reset() {
		super.reset();
		usedModels.clear();
		imports.clear();
	}

	/**
	 * @return the mappingModel
	 */
	public IFeatureModel getMappingModel() {
		return mappingModel;
	}

	public Map<String, UsedModel> getExternalModels() {
		return Collections.unmodifiableMap(usedModels);
	}

	/**
	 * @param mappingModel the mappingModel to set
	 */
	public void setMappingModel(IFeatureModel mappingModel) {
		this.mappingModel = mappingModel;
	}

	public void runTests() {
		final ExtendedFeatureModelAnalyzer analyzer = new ExtendedFeatureModelAnalyzer(this);
		Logger.logInfo(VELVET_FEATUREMODEL_IMPORTED);

		try {
			Logger.logInfo(analyzer.isValid() ? VALID : INVALID);
			StringBuilder sb = new StringBuilder("Dead Features: ");
			for (IFeature deadFeature : analyzer.getDeadFeatures()) {
				sb.append(deadFeature.getName() + ", ");
			}
			Logger.logInfo(sb.toString());
			sb.delete(0, sb.length());
			sb.append("FO Features: ");
			for (IFeature deadFeature : analyzer.getFalseOptionalFeatures()) {
				sb.append(deadFeature.getName() + ", ");
			}
			Logger.logInfo(sb.toString());
		} catch (final TimeoutException e) {
			Logger.logError(e);
		}
	}

	@Override
	@CheckForNull
	public IFeature getFeature(CharSequence name) {
		IFeature feature = super.getFeature(name);
		if (feature != null) {
			return feature;
		}

		if (name.toString().contains(".")) {
			return super.getFeature(this.getStructure().getRoot().getFeature().getName() + "." + name);
		} else {
			return null;
		}
	}

	public boolean isInterface() {
		return isInterface;
	}

	public void setInterface(boolean isInterface) {
		this.isInterface = isInterface;
	}

}
