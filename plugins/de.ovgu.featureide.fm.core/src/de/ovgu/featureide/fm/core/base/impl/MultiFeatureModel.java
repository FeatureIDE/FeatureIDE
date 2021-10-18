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
package de.ovgu.featureide.fm.core.base.impl;

import java.nio.file.Path;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import org.eclipse.core.runtime.IPath;
import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.constraint.Equation;
import de.ovgu.featureide.fm.core.constraint.FeatureAttributeMap;

/**
 * Adds attributes and attribute constraints to a feature model.
 *
 * @author Sebastian Krieter
 * @author Matthias Strauss
 */
public class MultiFeatureModel extends FeatureModel {

	public static class UsedModel {

		private final String modelName;
		private final String varName;
		/**
		 * The absolute path of the used model.
		 */
		private final Path path;
		private final int type;

		private String prefix;

		public UsedModel(UsedModel usedModel, String parentName, Path path) {
			modelName = usedModel.modelName;
			varName = parentName + usedModel.varName;
			this.path = path;
			type = usedModel.type;
		}

		public UsedModel(String modelName, String varName, Path path, int type) {
			this.modelName = modelName;
			this.varName = varName;
			this.path = path;
			this.type = type;
		}

		public String getModelName() {
			return modelName;
		}

		public String getVarName() {
			return varName;
		}

		/**
		 * @return The absolute path of the used model
		 */
		public Path getPath() {
			return path;
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
			return modelName + " " + varName + " [Path: " + path + "]"; // TODO #1250
		}
	}

	protected final FeatureAttributeMap<Integer> integerAttributes;
	protected final FeatureAttributeMap<Boolean> booleanAttributes;
	protected final FeatureAttributeMap<String> stringAttributes;

	protected final Map<String, UsedModel> usedModels;

	protected final List<Equation> attributeConstraints;
	protected final List<String> imports;
	protected final List<IConstraint> ownConstraints;

	protected IFeatureModel mappingModel;

	private boolean isInterface;

	public MultiFeatureModel(String factoryID) {
		super(factoryID);

		integerAttributes = new FeatureAttributeMap<>();
		booleanAttributes = new FeatureAttributeMap<>();
		stringAttributes = new FeatureAttributeMap<>();

		usedModels = new HashMap<>();

		attributeConstraints = new LinkedList<>();
		imports = new LinkedList<>();
		ownConstraints = new LinkedList<>();

		mappingModel = null;
		isInterface = false;
	}

	protected MultiFeatureModel(MultiFeatureModel extendedFeatureModel, IFeature newRoot) {
		super(extendedFeatureModel, newRoot);

		integerAttributes = new FeatureAttributeMap<>(extendedFeatureModel.integerAttributes);
		booleanAttributes = new FeatureAttributeMap<>(extendedFeatureModel.booleanAttributes);
		stringAttributes = new FeatureAttributeMap<>(extendedFeatureModel.stringAttributes);

		usedModels = new HashMap<>(extendedFeatureModel.usedModels);

		attributeConstraints = new LinkedList<>(extendedFeatureModel.attributeConstraints);
		imports = new LinkedList<>(extendedFeatureModel.imports);
		ownConstraints = new LinkedList<>(extendedFeatureModel.ownConstraints);

		mappingModel = extendedFeatureModel.mappingModel;

		isInterface = extendedFeatureModel.isInterface;
	}

	public List<String> getImports() {
		return imports;
	}

	public void setImports(List<String> imports) {
		this.imports.clear();
		imports.stream().forEach(importPath -> this.imports.add(importPath));
	}

	public void addImport(String imp) {
		imports.add(imp.replace(".", "\\"));
	}

	public void addAttribute(final String featureName, final String attributeName, final Boolean value) {
		booleanAttributes.setAttribute(featureName, attributeName, value);
	}

	public void addAttribute(final String featureName, final String attributeName, final Integer value) {
		integerAttributes.setAttribute(featureName, attributeName, value);
	}

	public void addAttribute(final String featureName, final String attributeName, final String value) {
		stringAttributes.setAttribute(featureName, attributeName, value);
	}

	public void addAttributeConstraint(final Equation constraint) {
		attributeConstraints.add(constraint);
	}

	@Override
	public void addConstraint(IConstraint constraint) {
		addOwnConstraint(constraint);
		elements.put(constraint.getInternalId(), constraint);
	}

	@Override
	public void addConstraint(IConstraint constraint, int index) {
		addOwnConstraint(constraint);
		elements.put(constraint.getInternalId(), constraint);
	}

	public void addOwnConstraint(final IConstraint constraint) {
		if (constraint instanceof MultiConstraint) {
			final MultiConstraint multiConstraint = (MultiConstraint) constraint;
			if (!multiConstraint.isFromExtern()) {
				ownConstraints.add(constraint);
			}
		}
		constraints.add(constraint);
	}

	/**
	 * Adds a parameter to the available parameters of the model
	 *
	 * @param varType the name of the interface that shall be bound to the variable
	 * @param varName the name of the variable an interface shall be bound to
	 * @param path
	 * @return true if the parameter could be added to the parameters. False if the variable name was already bound to another interface.
	 */
	public boolean addInterface(final String varType, final String varName, final Path path) {
		return addModel(varType, varName, path, MultiFeature.TYPE_INTERFACE);
	}

	public boolean addInstance(final String varType, final String varName, final Path path) {
		return addModel(varType, varName, path, MultiFeature.TYPE_INSTANCE);
	}

	public boolean addInheritance(final String varType, final String varName, final Path path) {
		return addModel(varType, varName, path, MultiFeature.TYPE_INHERITED);
	}

	public boolean addExternalModel(final UsedModel model) {
		if (usedModels.containsKey(model.varName)) {
			return false;
		} else {
			usedModels.put(model.varName, model);
			return true;
		}
	}

	private boolean addModel(final String varType, final String varName, final Path path, int modelType) {
		if (usedModels.containsKey(varName)) {
			return false;
		} else {
			usedModels.put(varName, new UsedModel(varType, varName, path, modelType));
			return true;
		}
	}

	public UsedModel getExternalModel(String varName) {
		return usedModels.get(varName);
	}

	public List<Equation> getAttributConstraints() {
		return attributeConstraints;
	}

	public FeatureAttributeMap<Boolean> getBooleanAttributes() {
		return booleanAttributes;
	}

	public FeatureAttributeMap<Integer> getIntegerAttributes() {
		return integerAttributes;
	}

	public FeatureAttributeMap<String> getStringAttributes() {
		return stringAttributes;
	}

	public List<IConstraint> getOwnConstraints() {
		return Collections.unmodifiableList(ownConstraints);
	}

	public void setOwnConstraints(List<IConstraint> ownConstraints) {
		this.ownConstraints.clear();
		ownConstraints.stream().forEach(constraint -> this.ownConstraints.add(constraint));
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
		for (final IFeature feature : featureTable.values()) {
			if ((feature instanceof MultiFeature) && ((MultiFeature) feature).isInstance()) {
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
		for (final IFeature feature : featureTable.values()) {
			if ((feature instanceof MultiFeature) && ((MultiFeature) feature).isInherited()) {
				return true;
			}
		}
		return false;
	}

	public boolean hasInterface() {
		for (final IFeature feature : featureTable.values()) {
			if ((feature instanceof MultiFeature) && ((MultiFeature) feature).isInterface()) {
				return true;
			}
		}
		return false;
	}

	@Override
	public void removeConstraint(IConstraint constraint) {
		ownConstraints.remove(constraint);
		super.removeConstraint(constraint);
	}

	@Override
	public void removeConstraint(int index) {
		ownConstraints.remove(constraints.get(index));
		super.removeConstraint(index);
	}

	@Override
	public void replaceConstraint(IConstraint constraint, int index) {
		super.replaceConstraint(constraint, index);
	}

	@Override
	public void setConstraint(int index, IConstraint constraint) {
		ownConstraints.remove(constraints.get(index));
		ownConstraints.add(constraint);
		super.setConstraint(index, constraint);
	}

	@Override
	public void reset() {
		super.reset();
		usedModels.clear();
		imports.clear();
		ownConstraints.clear();
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

	public void setExternalModels(Map<String, UsedModel> usedModels) {
		this.usedModels.clear();
		for (final Entry<String, UsedModel> entry : usedModels.entrySet()) {
			this.usedModels.put(entry.getKey(), new UsedModel(entry.getValue(), "", entry.getValue().path));
		}
	}

	/**
	 * @param mappingModel the mappingModel to set
	 */
	public void setMappingModel(IFeatureModel mappingModel) {
		this.mappingModel = mappingModel;
	}

	@Override
	public IFeature getFeature(CharSequence name) {
		final IFeature feature = super.getFeature(name);
		if (feature != null) {
			return feature;
		}

		if (name.toString().contains(".")) {
			return super.getFeature(getStructure().getRoot().getFeature().getName() + "." + name);
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

	@Override
	public FeatureModel clone() {
		return new MultiFeatureModel(this, null);
	}

	/**
	 * Returns all paths of imported submodels.
	 *
	 * @return new {@link List}
	 */
	public List<Path> getImportPaths() {
		return usedModels.values().stream().map(model -> model.getPath()).collect(Collectors.toList());
	}

	/**
	 * Extracts the model alias (key of a {@link UsedModel}) for an {@link MultiFeatureModel} that this model imports. This imported model is either stored
	 * directly in <code>event.source</code>, or can be found in the {@link IFeatureModelElement}
	 *
	 * @param event - {@link FeatureIDEEvent} A IMPORTED_MODEL_CHANGED event.
	 * @return String
	 */
	public String extractModelAlias(FeatureIDEEvent event) {
		// An IFeatureModel as source is its own element.
		IFeatureModel originalModel;
		if (event.getSource() instanceof IFeatureModel) {
			originalModel = (IFeatureModel) event.getSource();
		}
		// For an IFeatureModelElement, ask about its model instead.
		else if (event.getSource() instanceof IFeatureModelElement) {
			final IFeatureModelElement element = (IFeatureModelElement) event.getSource();
			originalModel = element.getFeatureModel();
		} else {
			return "";
		}

		// Look up the model alias by the path of the source model.
		final Path importedModelPath = originalModel.getSourceFile();
		String modelAlias = null;
		for (final Entry<String, UsedModel> entry : getExternalModels().entrySet()) {
			if (entry.getValue().getPath().equals(importedModelPath)) {
				modelAlias = entry.getKey() + ".";
				break;
			}
		}
		return modelAlias;
	}

	/**
	 * Tests if the given path has a reference as a model this composed model uses. If so, returns the alias of this path.
	 *
	 * @param path - {@link IPath} - A project-relative Eclipse path.
	 * @return {@link String}
	 */
	public String getReference(IPath path) {
		// Convert the project-relative path to a model reference.
		String modelString = path.removeTrailingSeparator().toString();
		modelString = modelString.split("\\.")[0];
		modelString = modelString.replace('/', '.');

		for (final Entry<String, UsedModel> entry : usedModels.entrySet()) {
			if (entry.getValue().modelName.equals(modelString)) {
				return entry.getKey();
			}
		}
		return null;
	}

	/**
	 * Rewrites the literals in the given {@link Node} <code>oldNode</code> as to append <code>modelAlias</code> to the literals/feature names. This way, we
	 * rewrite an imported constraint's formula whenever we create, remove or change it.
	 *
	 * @param oldNode - {@link Node}
	 * @param modelAlias - {@link String}
	 * @return new {@link Node}
	 */
	public Node rewriteNodeImports(Node oldNode, String modelAlias) {
		if (oldNode instanceof Literal) {
			final Literal literal = (Literal) oldNode;
			final String oldFeatureName = literal.getUniqueContainedFeatures().iterator().next();
			final String newFeatureName = modelAlias + oldFeatureName;
			return new Literal(newFeatureName, literal.positive);
		} else {
			final Node clonedNode = oldNode.clone();
			final Node[] oldChildren = clonedNode.getChildren();
			final Node[] newChildren = new Node[oldChildren.length];
			for (int iN = 0; iN < newChildren.length; iN++) {
				newChildren[iN] = rewriteNodeImports(oldChildren[iN], modelAlias);
			}
			clonedNode.setChildren(newChildren);
			return clonedNode;
		}
	}

	/**
	 * Reconstructs the structure of an imported feature model, starting from the given <code>oldStructure</code>, for this given feature model, that knows the
	 * imported model under the alias <code>modelAlias</code>.
	 *
	 * @param oldStructure - {@link IFeatureStructure}
	 * @param modelAlias - {@link String}
	 * @return new {@link IFeatureStructure}
	 */
	public IFeatureStructure reconstructStructure(IFeatureStructure oldStructure, String modelAlias) {
		// Create the new FeatureStructure for the correct feature.
		final IFeatureStructure structure = getFeature(modelAlias + oldStructure.getFeature().getName()).getStructure();
		// Copy mandatory, abstract and group type.
		structure.setAbstract(oldStructure.isAbstract());
		structure.setMandatory(oldStructure.isMandatory());
		if (oldStructure.isAlternative()) {
			structure.setAlternative();
		} else if (oldStructure.isAnd()) {
			structure.setAnd();
		} else if (oldStructure.isOr()) {
			structure.setOr();
		}
		// Repeat for other children, then return the structure.
		for (final IFeatureStructure child : oldStructure.getChildren()) {
			structure.addChild(reconstructStructure(child, modelAlias));
		}
		return structure;
	}

	/**
	 * Returns the constraint from the constraint list of this feature model that has the same propositional formula as <code>node</code>, and the same
	 * description text as <code>description</code>. This method is used to delete/modify imported constraints, because comparison by their ID does not work.
	 *
	 * @param newFormula - {@link Node}
	 * @param description - {@link String}
	 * @return c - {@link IConstraint}
	 */
	public IConstraint findConstraint(Node newFormula, String description) {
		for (final IConstraint constraint : getConstraints()) {
			if (newFormula.equals(constraint.getNode()) && description.equals(constraint.getDescription())) {
				return constraint;
			}
		}
		return null;
	}

	/**
	 * Updates the import lists and external model information with the values in <code>mfmReplacement</code>.
	 *
	 * @param mfmReplacement - {@link MultiFeatureModel}
	 */
	public void setMultiFeatureModelProperties(final MultiFeatureModel mfmReplacement) {
		setImports(mfmReplacement.getImports());
		setExternalModels(mfmReplacement.getExternalModels());

	}
}
