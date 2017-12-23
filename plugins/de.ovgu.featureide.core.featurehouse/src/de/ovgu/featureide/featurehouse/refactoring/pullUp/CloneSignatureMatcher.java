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
package de.ovgu.featureide.featurehouse.refactoring.pullUp;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sourceforge.pmd.cpd.Match;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.cloneanalysis.impl.CPDCloneAnalysis;
import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.results.CPDResultConverter;
import de.ovgu.featureide.cloneanalysis.results.CloneAnalysisResults;
import de.ovgu.featureide.cloneanalysis.results.VariantAwareClone;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.SignaturePosition;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringUtil;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;
import de.ovgu.featureide.fm.core.base.IFeature;
//import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.base.impl.Feature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class CloneSignatureMatcher {

	private final ProjectSignatures projectSignatures;
	private final IFeatureProject featureProject;
	private final AbstractClassSignature classSignature;
	private final String absoluteFileString;
	private final Map<AbstractSignature, List<ClonedFeatures>> clonedSignatures = new HashMap<>();

	public CloneSignatureMatcher(IFeatureProject featureProject, AbstractClassSignature signature, String absoluteFileString) {
		this.projectSignatures = featureProject.getProjectSignatures();
		this.featureProject = featureProject;
		this.classSignature = signature;
		this.absoluteFileString = absoluteFileString;
	}

	public Map<AbstractSignature, List<ClonedFeatures>> computeClonedSignatures() {
		final IPath absoluteFilePath = Path.fromOSString(absoluteFileString);

		final CloneAnalysisResults<VariantAwareClone> cloneResults = getCloneResults(absoluteFilePath.toFile().getName());

		final Set<AbstractSignature> matchedSignatures = RefactoringUtil.getIncludedMatchingSignaturesForFile(classSignature, absoluteFileString);
//		removeConstructors(matchedSignatures);

		for (VariantAwareClone clone : cloneResults.getClones()) {

			for (AbstractSignature method : matchedSignatures) {
				addClonedSignatures(method, clone);
			}
		}

		Set<AbstractSignature> removableSignatures = new HashSet<>();
		for (Entry<AbstractSignature, List<ClonedFeatures>> entry : clonedSignatures.entrySet()) {

			IFeature feature = getFeatureForSignature(entry.getKey());
			Set<ClonedFeatures> removableClonedFeatures = new HashSet<>();
			for (ClonedFeatures clonedFeatures : entry.getValue()) {
				if (!clonedFeatures.getFeatures().contains(feature) || clonedFeatures.getFeatures().size() < 2) removableClonedFeatures.add(clonedFeatures);
			}

			for (ClonedFeatures clonedFeatures : removableClonedFeatures) {
				entry.getValue().remove(clonedFeatures);
			}

			if (entry.getValue().isEmpty()) removableSignatures.add(entry.getKey());
		}

		for (AbstractSignature abstractSignature : removableSignatures) {
			clonedSignatures.remove(abstractSignature);
		}

		return clonedSignatures;
	}

	private void removeConstructors(Set<AbstractSignature> matchedSignatures) {

		Set<AbstractSignature> removableConstructors = new HashSet<>();
		for (AbstractSignature signature : matchedSignatures) {
			if ((signature instanceof FujiMethodSignature) && ((FujiMethodSignature) signature).isConstructor()) removableConstructors.add(signature);
		}

		matchedSignatures.removeAll(removableConstructors);
	}

	private IFeature getFeatureForSignature(AbstractSignature signature) {
		for (AFeatureData featureData : signature.getFeatureData()) {
			if (featureData.getAbsoluteFilePath().equals(absoluteFileString)) return RefactoringUtil.getFeatureForId(projectSignatures, featureData.getID());
		}
		return null;
	}

	private Map<IPath, AFeatureData> getIncludesFileForSignature(AbstractSignature sig) {
		Map<IPath, AFeatureData> includesFiles = new HashMap<>();
		for (AFeatureData featureData : sig.getFeatureData()) {
			includesFiles.put(Path.fromOSString(featureData.getAbsoluteFilePath()), featureData);
		}

		return includesFiles;
	}

	private void addClonedSignatures(final AbstractSignature signature, final VariantAwareClone clone) {

		final Map<IPath, AFeatureData> includedFiles = getIncludesFileForSignature(signature);

		ClonedFeatures clonedFeatures = new ClonedFeatures();

		for (CloneOccurence cloneOccurence : clone.getOccurences()) {

			if (!includedFiles.containsKey(cloneOccurence.getFile())) continue;

			final AFeatureData featureData = includedFiles.get(cloneOccurence.getFile());
			final Feature feature = (Feature) RefactoringUtil.getFeatureForId(projectSignatures, featureData.getID());

			final int startRow = cloneOccurence.getStartIndex();
			final int endRow = startRow + cloneOccurence.getClone().getLineCount() - 1;

			if (isClonedSignature(featureData, startRow, endRow)) {
				clonedFeatures.addFeature(feature);
			}
		}

		if (!clonedFeatures.getFeatures().isEmpty()) addFeatureForSignature(signature, clonedFeatures);
	}

	private void addFeatureForSignature(final AbstractSignature signature, final ClonedFeatures clonedFeatures) {
		final List<ClonedFeatures> features;
		if (clonedSignatures.containsKey(signature)) features = clonedSignatures.get(signature);
		else {
			features = new ArrayList<>();
			clonedSignatures.put(signature, features);
		}

		addClonedFeatures(features, clonedFeatures);
//		if (!features.contains(clonedFeatures))
//			features.add(clonedFeatures);
	}

	private void addClonedFeatures(final List<ClonedFeatures> list, final ClonedFeatures clonedfeatures) {
		for (ClonedFeatures features : list) {

			final Set<Feature> listFeatures1 = features.getFeatures();
			final Set<Feature> listFeatures2 = clonedfeatures.getFeatures();

			if (listFeatures1.size() == listFeatures2.size() && listFeatures1.containsAll(listFeatures2)) return;

			if (listFeatures1.size() > listFeatures2.size() && listFeatures1.containsAll(listFeatures2)) return;

			if (listFeatures1.size() < listFeatures2.size() && listFeatures2.containsAll(listFeatures1)) {
				list.remove(features);
				list.add(clonedfeatures);
				return;
			}
		}

		list.add(clonedfeatures);
	}

	private boolean isClonedSignature(final AFeatureData featureData, final int startRow, final int endRow) {
		final SignaturePosition position = featureData.getSigPosition();
		if ((position.getStartRow() >= startRow) && (position.getEndRow() <= endRow)) return true;

		return false;
	}

	private CloneAnalysisResults<VariantAwareClone> getCloneResults(String filteredName) {
		CPDCloneAnalysis analysis = new CPDCloneAnalysis(filteredName);
		final Iterator<Match> cpdResults = analysis.analyze(featureProject.getProject());
		return CPDResultConverter.convertMatchesToReadableResults(cpdResults);
	}

	public Map<AbstractSignature, List<ClonedFeatures>> getClonedSignatures() {
		return clonedSignatures;
	}
}
