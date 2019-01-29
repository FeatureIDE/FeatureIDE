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
package de.ovgu.featureide.fm.core;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.prop4j.Node;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Contains all deprecated functionality of {@link IFeatureModel}.
 *
 * @author Jens Meinicke
 */
abstract class DeprecatedFeatureModel {

	public abstract FeatureModelAnalyzer getAnalyser();

	public abstract IFeatureModelLayout getLayout();

	public abstract RenamingsManager getRenamingsManager();

	abstract FMComposerManager getFMComposerManager(final IProject project);

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#analyzeFeatureModel(de.ovgu.featureide.fm.core.job.monitor.IMonitor)}
	 *             instead.
	 */
	@Deprecated
	public HashMap<Object, Object> analyzeFeatureModel() {
		return getAnalyser().analyzeFeatureModel(null);
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#isValid()} instead.
	 */
	@Deprecated
	public boolean isValid() throws TimeoutException {
		return getAnalyser().isValid();
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#checkImplies(java.util.Collection, java.util.Collection)} instead.
	 */
	@Deprecated
	public boolean checkImplies(Set<IFeature> a, Set<IFeature> b) throws TimeoutException {
		return getAnalyser().checkImplies(a, b);
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#checkCondition(Node)} instead.
	 */
	@Deprecated
	public boolean checkCondition(Node condition) {
		return getAnalyser().checkCondition(condition);
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#areMutualExclusive(java.util.Collection, java.util.Collection)} instead.
	 */
	@Deprecated
	public boolean areMutualExclusive(Set<IFeature> context, List<Set<IFeature>> featureSets) throws TimeoutException {
		return getAnalyser().areMutualExclusive(context, featureSets);
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#mayBeMissing(java.util.Collection, java.util.Collection)} instead.
	 */
	@Deprecated
	public boolean mayBeMissing(Set<IFeature> context, List<Set<IFeature>> featureSets) throws TimeoutException {
		return getAnalyser().mayBeMissing(context, featureSets);
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#exists(java.util.Collection)} instead.
	 */
	@Deprecated
	public boolean exists(Set<IFeature> features) throws TimeoutException {
		return getAnalyser().exists(features);
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#conjunct(java.util.Collection)} instead.
	 */
	@Deprecated
	public Node conjunct(Set<IFeature> b) {
		return getAnalyser().conjunct(b);
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#countConcreteFeatures()} instead.
	 */
	@Deprecated
	public int countConcreteFeatures() {
		return getAnalyser().countConcreteFeatures();
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#countHiddenFeatures()} instead.
	 */
	@Deprecated
	public int countHiddenFeatures() {
		return getAnalyser().countHiddenFeatures();
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#countTerminalFeatures()} instead.
	 */
	@Deprecated
	public int countTerminalFeatures() {
		return getAnalyser().countTerminalFeatures();
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#commonFeatures(long, Object...)} instead.
	 */
	@Deprecated
	public LinkedList<String> commonFeatures(long timeout, Object... selectedFeatures) {
		return new LinkedList<String>(getAnalyser().commonFeatures(timeout, selectedFeatures));
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#getDeadFeatures()} instead.
	 */
	@Deprecated
	public LinkedList<IFeature> getDeadFeatures() {
		return new LinkedList<IFeature>(getAnalyser().getDeadFeatures());
	}

	/**
	 * @deprecated Will be removed in a future release. Use <br><code>Use FeatureModelLayout.getLegendPos()</code><br> instead.
	 */
	@Deprecated
	public FMPoint getLegendPos() {
//	    return getLayout().getLegendPos();
		return null;
	}

	/**
	 * @deprecated Will be removed in a future release. Use <br><code>Use FeatureModelLayout.setLegendPos(int, int)</code><br> instead.
	 */
	@Deprecated
	public void setLegendPos(int x, int y) {
//	    getLayout().setLegendPos(x, y);
	}

	/**
	 * @deprecated Will be removed in a future release. Use <br><code>Use FeatureModelLayout.setLegendAutoLayout(boolean)</code><br> instead.
	 */
	@Deprecated
	public void setLegendAutoLayout(boolean b) {
//	    getLayout().setLegendAutoLayout(b);
	}

	/**
	 * @deprecated Will be removed in a future release. Use <br><code>Use FeatureModelLayout.hasLegendAutoLayout()</code><br> instead.
	 */
	@Deprecated
	public boolean hasLegendAutoLayout() {
//	    return getLayout().hasLegendAutoLayout();
		return false;
	}

	/**
	 * @deprecated Will be removed in a future release. Use <br><code>Use FeatureModelLayout.hasFeaturesAutoLayout()</code><br> instead.
	 */
	@Deprecated
	public boolean hasFeaturesAutoLayout() {
//	    return getLayout().hasFeaturesAutoLayout();
		return false;
	}

	/**
	 * @deprecated Will be removed in a future release. Use <br><code>Use FeatureModelLayout.showHiddenFeature()</code><br> instead.
	 */
	@Deprecated
	public boolean showHiddenFeatures() {
//	    return getLayout().showHiddenFeatures();
		return false;
	}

	/**
	 * @deprecated Will be removed in a future release. Use <br><code>Use FeatureModelLayout.showHiddenFeatures(boolean)</code><br> instead.
	 */
	@Deprecated
	public void showHiddenFeatures(boolean b) {
//	    getLayout().showHiddenFeatures(b);
	}

	/**
	 * @deprecated Will be removed in a future release. Use <br><code>Use FeatureModelLayout.verticalLayout()</code><br> instead.
	 */
	@Deprecated
	public boolean verticalLayout() {
//	    return getLayout().verticalLayout();
		return false;
	}

	/**
	 * @deprecated Will be removed in a future release. Use <br><code>Use FeatureModelLayout.verticalLayout(boolean)</code><br> instead.
	 */
	@Deprecated
	public void verticalLayout(boolean b) {
//	    getLayout().verticalLayout(b);
	}

	@Deprecated
	public boolean hasDead() {
		return getDeadFeatures().size() > 0;
	}

	/**
	 * @deprecated Will be removed in a future release. Use <br><code>Use FeatureModelLayout.setLayout(int)</code><br> instead.
	 */
	@Deprecated
	public void setLayout(int newLayoutAlgorithm) {
//	    getLayout().setLayout(newLayoutAlgorithm);
	}

	/**
	 * @deprecated Will be removed in a future release. <br><code>Use FeatureModelLayout.getLayoutAlgorithm()</code><br> instead.
	 */
	@Deprecated
	public int getLayoutAlgorithm() {
//	    return getLayout().getLayoutAlgorithm();
		return 0;
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link RenamingsManager#getOldName(String)} instead.
	 */
	@Deprecated
	public String getOldName(String name) {
		return getRenamingsManager().getOldName(name);
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link RenamingsManager#getNewName(String)} instead.
	 */
	@Deprecated
	public String getNewName(String name) {
		return getRenamingsManager().getNewName(name);
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link RenamingsManager#renameFeature(String, String)} instead.
	 */
	@Deprecated
	public void renameFeature(String oldName, String newName) {
		getRenamingsManager().renameFeature(oldName, newName);
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link RenamingsManager#performRenamings()} instead.
	 */
	@Deprecated
	public void performRenamings() {
		getRenamingsManager().notifyAboutRenamings();
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link RenamingsManager#isRenamed()} instead.
	 */
	@Deprecated
	public boolean isRenamed() {
		return getRenamingsManager().isRenamed();
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link RenamingsManager#performRenamings(java.io.File)} instead.
	 */
	@Deprecated
	public void performRenamings(IFile file) {
		getRenamingsManager().notifyAboutRenamings();
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link RenamingsManager#getOldFeatureNames()} instead.
	 */
	@Deprecated
	public Set<String> getOldFeatureNames() {
		return getRenamingsManager().getOldFeatureNames();
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FMComposerManager#setComposerID(String, Object)} instead.
	 */
	@Deprecated
	public void setComposerID(String string, FMComposerExtension comp) {
		getFMComposerManager(null).setComposerID(string, comp);
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#getCachedDeadFeatures()} instead.
	 */
	@Deprecated
	public LinkedList<IFeature> getCalculatedDeadFeatures() {
		return new LinkedList<IFeature>(getAnalyser().getCachedDeadFeatures());
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#valid()} instead.
	 */
	@Deprecated
	public boolean valid() {
		return getAnalyser().valid();
	}

	/**
	 * @deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#getCachedFalseOptionalFeatures()} instead. Or use
	 *             {@link FeatureModelAnalyzer#getFalseOptionalFeatures()} to recalculate false optional features.
	 */
	@Deprecated
	public LinkedList<IFeature> getFalseOptionalFeatures() {
		return new LinkedList<IFeature>(getAnalyser().getCachedFalseOptionalFeatures());
	}
}
