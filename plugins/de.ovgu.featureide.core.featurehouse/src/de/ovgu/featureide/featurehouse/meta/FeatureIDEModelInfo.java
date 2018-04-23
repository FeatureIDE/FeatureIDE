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
package de.ovgu.featureide.featurehouse.meta;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;

import org.prop4j.Node;
import org.prop4j.NodeWriter;

import composer.rules.meta.FeatureModelInfo;
import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.configuration.SelectionNotPossibleException;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;

/**
 * Representation of the feature model. This class is accessed by FeatureHouse to get information about the feature model.
 *
 * @author Matthias Praast
 * @author Marcus Pinnecke (Feature Interface)
 */
public class FeatureIDEModelInfo implements FeatureModelInfo {

	private final IFeatureModel featureModel;
	private final Configuration currentConfig;
	private List<String> coreFeatureNames;
	private boolean validSelect = true;
	private boolean validReject = true;
	private HashMap<String, HashMap<String, List<IFeature>>> rootsForMethod = new HashMap<String, HashMap<String, List<IFeature>>>();

	private final boolean obligatory = true;
	private final boolean obligatoryMethod = true;
	private final boolean fm = true;// ??
	private final String validClause;
	private final boolean useValidMethod;

	/**
	 * @param useValidMethod Defines whether the valid() or the complete formula is used as requieres clause.
	 */
	public FeatureIDEModelInfo(final IFeatureModel featureModel, final boolean useValidMethod) {
		this.featureModel = featureModel;
		this.useValidMethod = useValidMethod;
		currentConfig = new Configuration(featureModel);
		validClause = createdValidClause();
	}

	private String createdValidClause() {
		final AdvancedNodeCreator nc = new AdvancedNodeCreator(featureModel);
		nc.setCnfType(CNFType.Compact);
		nc.setIncludeBooleanValues(false);
		final Node nodes = nc.createNodes().eliminateNotSupportedSymbols(NodeWriter.javaSymbols);
		String formula = " " + nodes.toString(NodeWriter.javaSymbols).toLowerCase(Locale.ENGLISH);

		for (final CharSequence feature : FeatureUtils.extractFeatureNames(featureModel.getFeatures())) {
			formula = formula.replaceAll("([\\s,\\(])" + feature.toString().toLowerCase(Locale.ENGLISH),
					"$1FM.FeatureModel." + feature.toString().toLowerCase(Locale.ENGLISH));
		}
		return formula.trim();
	}

	@Override
	public boolean isCoreFeature(String featureName) {
		if (!obligatory) {
			return false;
		}
		if (coreFeatureNames == null) {
			final Configuration newConfig = new Configuration(featureModel);
			coreFeatureNames = new LinkedList<String>();
			for (final IFeature feature : newConfig.getSelectedFeatures()) {
				coreFeatureNames.add(feature.getName());
			}
		}

		return coreFeatureNames.contains(featureName);
	}

	@Override
	public boolean isCoreFeature(String featureName, boolean useSelection) {
		if (!obligatory) {
			return false;
		}
		if (!useSelection) {
			return isCoreFeature(featureName);
		}

		for (final IFeature feature : currentConfig.getSelectedFeatures()) {
			if (feature.getName().equals(featureName)) {
				return true;
			}
		}

		return false;
	}

	@Override
	public boolean isMethodCoreFeature(String className, String methodName, String featureName) {
		if (!obligatoryMethod) {
			return false;
		}
		final HashMap<String, List<IFeature>> methodFeatures = rootsForMethod.get(className);
		if (methodFeatures == null) {
			return false;
		}
		final List<IFeature> features = methodFeatures.get(methodName);
		if (features == null) {
			return false;
		}
		for (final IFeature rootFeature : features) {
			if (!rootFeature.getName().equals(featureName)) {
				final Configuration config = new Configuration(featureModel);
				config.setManual(rootFeature.getName(), Selection.SELECTED);
				if (config.getSelectablefeature(featureName).getAutomatic() != Selection.SELECTED) {
					return false;
				}
			}
		}

		return true;

	}

	@Override
	public boolean isMethodCoreFeature(String className, String methodName, String featureName, boolean useSelection) {
		if (!obligatoryMethod) {
			return false;
		}
		if (!useSelection) {
			return isMethodCoreFeature(className, methodName, featureName);
		}

		final HashMap<String, List<IFeature>> methodFeatures = rootsForMethod.get(className);
		if (methodFeatures == null) {
			return false;
		}
		final List<IFeature> features = methodFeatures.get(methodName);
		if (features == null) {
			return false;
		}
		for (final IFeature rootFeature : features) {
			if (!rootFeature.getName().equals(featureName)) {
				final Configuration config = new Configuration(featureModel);
				for (final IFeature feat : currentConfig.getSelectedFeatures()) {
					config.setManual(feat.getName(), Selection.SELECTED);
				}
				for (final IFeature feat : currentConfig.getUnSelectedFeatures()) {
					config.setManual(feat.getName(), Selection.UNSELECTED);
				}
				config.setManual(rootFeature.getName(), Selection.SELECTED);
				if (config.getSelectablefeature(featureName).getAutomatic() != Selection.SELECTED) {
					return false;
				}
			}
		}

		return true;
	}

	@Override
	public void selectFeature(String featureName) {
		if (!fm) {
			return;
		}
		try {
			currentConfig.setManual(featureName, Selection.SELECTED);
		} catch (final SelectionNotPossibleException ex) {
			validSelect = false;
		}
	}

	@Override
	public void eliminateFeature(String featureName) {
		if (!fm) {
			return;
		}
		try {
			currentConfig.setManual(featureName, Selection.UNSELECTED);
		} catch (final SelectionNotPossibleException ex) {
			validReject = false;
		}
	}

	@Override
	public void resetSelections() {
		if (!fm) {
			return;
		}
		for (final IFeature feature : currentConfig.getSelectedFeatures()) {
			currentConfig.setManual(feature.getName(), Selection.UNDEFINED);
		}
		validSelect = true;

	}

	@Override
	public void resetEliminations() {
		if (!fm) {
			return;
		}
		for (final IFeature feature : currentConfig.getUnSelectedFeatures()) {
			currentConfig.setManual(feature.getName(), Selection.UNDEFINED);
		}
		validReject = true;
	}

	@Override
	public void reset() {
		if (!fm) {
			return;
		}
		currentConfig.resetValues();
		validSelect = true;
		validReject = true;
	}

	@Override
	public boolean isValidSelection() {
		if (!fm) {
			return true;
		}
		return validSelect && validReject && (currentConfig.canBeValid());
	}

	@Override
	public boolean canBeSelected(String featureName) {
		if (!fm) {
			return true;
		}
		final SelectableFeature feature = currentConfig.getSelectablefeature(featureName);
		final Selection oldManual = feature.getManual();
		try {
			currentConfig.setManual(feature, Selection.SELECTED);
			currentConfig.setManual(feature, oldManual);
			return true;
		} catch (final SelectionNotPossibleException ex) {
			return false;
		}
	}

	@Override
	public boolean canBeEliminated(String featureName) {
		if (!fm) {
			return true;
		}
		final SelectableFeature feature = currentConfig.getSelectablefeature(featureName);
		final Selection oldManual = feature.getManual();
		try {
			currentConfig.setManual(feature, Selection.UNSELECTED);
			currentConfig.setManual(feature, oldManual);
			return true;
		} catch (final SelectionNotPossibleException ex) {
			return false;
		}
	}

	@Override
	public boolean isAlwaysSelected(String featureName) {
		if (!fm) {
			return false;
		}
		return currentConfig.getSelectablefeature(featureName).getSelection() == Selection.SELECTED;
	}

	@Override
	public boolean isAlwaysEliminated(String featureName) {
		if (!fm) {
			return false;
		}
		return currentConfig.getSelectablefeature(featureName).getSelection() == Selection.UNSELECTED;
	}

	@Override
	public void addFeatureNodes(List<FSTNonTerminal> features) {
		if (!obligatoryMethod) {
			return;
		}
		rootsForMethod = new HashMap<String, HashMap<String, List<IFeature>>>();
		for (final FSTNonTerminal featureNode : features) {
			final String featureName = getFeatureName(featureNode);

			// get all method-Nodes
			for (final FSTNode methodNode : getMethodNodes(featureNode)) {
				final String className = getClassName(methodNode);
				final String methodName = getMethodName(methodNode);

				HashMap<String, List<IFeature>> methodFeature = rootsForMethod.get(className);
				if (methodFeature == null) {
					methodFeature = new HashMap<String, List<IFeature>>();
					rootsForMethod.put(className, methodFeature);
				}

				List<IFeature> featureList = methodFeature.get(methodName);
				if (featureList == null) {
					featureList = new LinkedList<IFeature>();
					methodFeature.put(methodName, featureList);
				}

				if (!featureList.contains(featureModel.getFeature(featureName))) {
					addToFeatureList(featureModel.getFeature(featureName), featureList);
				}
			}
		}
	}

	private String getMethodName(FSTNode methodNode) {
		if (methodNode == null) {
			return "";
		}
		if (methodNode.getType().contains("MethodDeclaration")) {
			String name = methodNode.getName();
			if (name.contains("(")) {
				name = name.substring(0, name.indexOf("(")).trim();
			}
			return name;
		}
		return getMethodName(methodNode.getParent());
	}

	private String getClassName(FSTNode methodNode) {
		if (methodNode == null) {
			return "";
		}
		if (methodNode.getType().contains("ClassDeclaration")) {
			return methodNode.getName();
		}
		return getClassName(methodNode.getParent());
	}

	private List<FSTNode> getMethodNodes(FSTNode featureNode) {
		final LinkedList<FSTNode> result = new LinkedList<FSTNode>();
		if (featureNode == null) {
			return result;
		}
		if (featureNode.getType().contains("MethodDeclaration")) {
			result.add(featureNode);
			return result;
		}
		if (!(featureNode instanceof FSTNonTerminal)) {
			return result;
		}

		for (final FSTNode child : ((FSTNonTerminal) featureNode).getChildren()) {
			result.addAll(getMethodNodes(child));
		}

		return result;
	}

	private String getFeatureName(FSTNode featureNode) {
		return featureNode.getName();
	}

	@Override
	public void clearFeatureNodes() {
		rootsForMethod.clear();
	}

	private void addToFeatureList(IFeature feature, List<IFeature> featureList) {
		if (!featureList.contains(feature)) {
			featureList.add(feature);
		}
	}

	@Override
	public String getValidClause() {
		if (useValidMethod) {
			return "FM.FeatureModel.valid()";
		} else {
			return validClause;
		}
	}

}
