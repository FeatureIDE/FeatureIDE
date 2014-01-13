/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.core.constraint.Equation;
import de.ovgu.featureide.fm.core.constraint.FeatureAttributeMap;

/**
 * Adds attributes and attribute constraints to a feature model.
 * 
 * @author Sebastian Krieter
 * @author Matthias Strauss
 */
public class ExtendedFeatureModel
	extends
		FeatureModel {

	protected FeatureAttributeMap<Integer> integerAttributes = new FeatureAttributeMap<Integer>();
	protected FeatureAttributeMap<Boolean> booleanAttributes = new FeatureAttributeMap<Boolean>();
	protected FeatureAttributeMap<String> stringAttributes = new FeatureAttributeMap<String>();
	protected Map<String, String> parameters = new HashMap<String, String>();
	protected Set<Feature> inheritedFeatures = new HashSet<Feature>();
	protected Set<String> parents = new HashSet<String>();
	protected Map<String, String> instances = new HashMap<String, String>();
	protected boolean hasParameters = false;

	protected LinkedList<Equation> attributeConstraints = new LinkedList<Equation>();

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
	 * Adds a mapping for an instancename to the model which it will be bound to
	 * 
	 * @param name the name of the variable
	 * @param model the model that the variable is bound to
	 */
	public void addInstanceMapping(final String name, final String model) {
		this.instances.put(name, model);
	}

	/**
	 * Adds a parameter to the available parameters of the model
	 * 
	 * @param interfaceClazz the name of the interface that shall be bound to
	 *            the variable
	 * @param varName the name of the variable an interface shall be bound to
	 * @return true if the parameter could be added to the parameters. False if
	 *         the variable name was already bound to another interface.
	 */
	public boolean addParameter(final String interfaceClazz, final String varName) {
		if (this.parameters.containsKey(varName)) {
			return false;
		}

		if (!this.hasParameters) {
			this.hasParameters = true;
		}

		this.parameters.put(varName, interfaceClazz);
		return true;
	}

	/**
	 * Adds the name of a Model as a parent of the current model.
	 * 
	 * @param parentModelName the name of the parent model
	 */
	public void addParent(final String parentModelName) {
		this.parents.add(parentModelName);
	}

	public LinkedList<Equation> getAttributConstraints() {
		return this.attributeConstraints;
	}

	public FeatureAttributeMap<Boolean> getBooleanAttributes() {
		return this.booleanAttributes;
	}

	/**
	 * returns a copy of the internal mappings of instances and their names.
	 * 
	 * @return a copy of the internal mappings of instances and their names.
	 */
	public Map<String, String> getInstanceMappings() {
		return new HashMap<String, String>(this.instances);
	}

	public FeatureAttributeMap<Integer> getIntegerAttributes() {
		return this.integerAttributes;
	}

	/**
	 * The result is not supposed to be edited, since only a copy of the
	 * original Map is returned
	 * 
	 * @return a copy of the internal collection of parameters. The returned
	 *         value is not supposed to be edited.
	 */
	public Map<String, String> getParameters() {
		return new HashMap<String, String>(this.parameters);
	}

	/**
	 * returns a set containing the parentmodels of the current model.
	 * 
	 * @return a copy of the parents of the model
	 */
	public Set<String> getParents() {
		return new HashSet<String>(this.parents);
	}

	public FeatureAttributeMap<String> getStringAttributes() {
		return this.stringAttributes;
	}

	/**
	 * This method is used by the mspl plugin to determine if a model uses
	 * interfaces. The first parameter that is added will set hasParameters to
	 * true.
	 * 
	 * @return if the model has interface parameters specified
	 */
	public boolean hasParameters() {
		return this.hasParameters;
	}

	/**
	 * Returns the name of the implemented interface or an empty String if no
	 * interfaces are implemented.
	 * 
	 * @return the name of the implemented interface or an empty String if no
	 *         interfaces are implemented.
	 */
	public String implementsInterface() {
		return "";
	}

	/**
	 * Checks if a given Feature in this model was inherited.
	 * 
	 * @param inherited the feature for which it will be checked if it is
	 *            inherited
	 * @return true if and only if the feature was inherited
	 */
	public boolean isInherited(final Feature inherited) {
		return this.inheritedFeatures.contains(inherited);
	}

	/**
	 * This method stores inherited features.
	 * 
	 * @param inherited the exact feature, that was added to the featuremodel
	 *            previously
	 */
	public void setFeatureInherited(final Feature inherited) {
		this.inheritedFeatures.add(inherited);
	}
}
