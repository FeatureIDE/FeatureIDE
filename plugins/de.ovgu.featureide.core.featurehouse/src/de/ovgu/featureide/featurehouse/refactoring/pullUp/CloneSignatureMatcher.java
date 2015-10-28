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
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class CloneSignatureMatcher {

	private final ProjectSignatures projectSignatures;
	private final IFeatureProject featureProject;
	private final AbstractClassSignature signature;
	
	private final String absoluteFileString;
	
	public CloneSignatureMatcher(ProjectSignatures projectSignatures, IFeatureProject featureProject,
			AbstractClassSignature signature, String absoluteFileString) {
		this.projectSignatures = projectSignatures;
		this.featureProject = featureProject;
		this.signature = signature;
		this.absoluteFileString = absoluteFileString;
	}
	
	public Map<AbstractSignature, List<Feature>> getMatchedClonedSignatures()
	{
		final IPath absoluteFilePath = Path.fromOSString(absoluteFileString);

		final Map<AbstractSignature, List<Feature>> filteredClonedSignatures = new HashMap<>();
		final CloneAnalysisResults<VariantAwareClone> cloneResults = getCloneResults(absoluteFilePath.toFile().getName());
		
		for (VariantAwareClone clone : cloneResults.getClones()) {
			
			final Set<AbstractSignature> clonedSignatures = getClonedSignatures(absoluteFilePath, clone);
			
			addFilteredClonedSignatures(filteredClonedSignatures, clone, clonedSignatures);
		}
		
		return  filteredClonedSignatures;
	}

	private void addFilteredClonedSignatures(final Map<AbstractSignature, List<Feature>> filteredClonedSignatures, 
			final VariantAwareClone clone, final Set<AbstractSignature> clonedSignatures) {

		for (AbstractSignature abstractSignature : clonedSignatures) {
			
			final List<Feature> features;
			if (filteredClonedSignatures.containsKey(abstractSignature))
				features = filteredClonedSignatures.get(abstractSignature);
			else
			{
				features = new ArrayList<>();
				filteredClonedSignatures.put(abstractSignature, features);
			}
				
			addFeatures(clone, abstractSignature, features);
		}
	}

	private void addFeatures(final VariantAwareClone clone, AbstractSignature abstractSignature, final List<Feature> features) {
		for (AFeatureData featureData : abstractSignature.getFeatureData()) {
			IPath absFile = Path.fromOSString(featureData.getAbsoluteFilePath());
			if (clone.getDistinctFiles().contains(absFile))
			{
				features.add(RefactoringUtil.getFeatureForId(projectSignatures, featureData.getID()));
			}
		}
	}

	private Set<AbstractSignature> getClonedSignatures(final IPath absoluteFilePath, final VariantAwareClone clone) {
		final Set<AbstractSignature> clonedSignatures = new HashSet<>();
		
		for (CloneOccurence cloneOccurence : clone.getOccurences()) {
			if (!cloneOccurence.getFile().equals(absoluteFilePath)) continue;

			clonedSignatures.addAll(getClonedSignatures(signature.getMethods(), cloneOccurence));
			clonedSignatures.addAll(getClonedSignatures(signature.getFields(), cloneOccurence));
			clonedSignatures.addAll(getClonedSignatures(signature.getMemberClasses(), cloneOccurence));
		}
		
		return clonedSignatures;
	}
		
	private Set<AbstractSignature> getClonedSignatures(final Set<? extends AbstractSignature> signatures, final CloneOccurence cloneOccurence) {
		final Set<AbstractSignature> clonedSignatures = new HashSet<>();
		
		final int startRow = cloneOccurence.getStartIndex();
		final int endRow = startRow + cloneOccurence.getClone().getLineCount();

		for (AbstractSignature sig : signatures) {
			 if (isClonedSignature(sig, startRow, endRow)) clonedSignatures.add(sig); 
		}
		
		return clonedSignatures;
	}
	
	private boolean isClonedSignature(final AbstractSignature signature, final int startRow, final int endRow)
	{
		for (AFeatureData featureData : signature.getFeatureData()) {
			final SignaturePosition position = featureData.getSigPosition();
			if (featureData.getAbsoluteFilePath().equals(absoluteFileString) && (position.getStartRow() >= startRow) && (position.getEndRow() <= endRow)) 
				return true;
		}
		
		return false;
	}

	
	private CloneAnalysisResults<VariantAwareClone> getCloneResults(String filteredName){
		CPDCloneAnalysis analysis = new CPDCloneAnalysis(filteredName);
		final Iterator<Match> cpdResults = analysis.analyze(featureProject.getProject());
		return CPDResultConverter.convertMatchesToReadableResults(cpdResults);
	}
}
