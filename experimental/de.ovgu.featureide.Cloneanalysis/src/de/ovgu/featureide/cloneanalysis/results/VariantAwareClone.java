package de.ovgu.featureide.cloneanalysis.results;

import java.util.HashSet;
import java.util.Set;
import java.util.Map.Entry;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.views.CloneVariantType;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.Feature;

public class VariantAwareClone extends Clone
{

	private Set<Feature> relevantFeatures = null;
	private CloneVariantType cloneVariantType = CloneVariantType.UNDEFINED;

	public VariantAwareClone(Set<CloneOccurence> occurences, int lines, int tokens, int files,
			String code)
	{
		super(occurences, lines, tokens, files, code);
		calculateVariantAwareness();
	}

	/**
	 * Calculates the {@link CloneVariantType} for this Clone. Also updates
	 * {@link #relevantFeatures}, if the clone is detected in a FeatureProject.
	 * 
	 */
	private void calculateVariantAwareness()
	{
		checkForCrossProjectOccurences();

		// case: all occurences are within a single project. They might occur in
		// different features though.
		if (cloneVariantType == CloneVariantType.INTRAVARIANT)
			testForCrossFeatureOccurences();

	}

	private void testForCrossFeatureOccurences()
	{
		IFeatureProject featureProject = CorePlugin.getFeatureProject(relevantProjects.iterator()
				.next());
		for (Entry<CloneOccurence, IFile> entry : occurences.entrySet())
		{
			// Case comparing resources of different featureproject; Not
			// supported. Does it even make sense to support it?
			if (CorePlugin.getFeatureProject(entry.getValue()) != featureProject)
				throw new UnsupportedOperationException(
						"comparing resources of different featureprojects is not supported(yet?)");

			addRelevantFeature(featureProject, entry.getKey());

		}
	}

	/**
	 * Adds the Feature, of which the occurence is a part of to the field
	 * {@link #relevantFeatures}.
	 * 
	 * @param featureProject
	 * @param occurence
	 */
	private void addRelevantFeature(IFeatureProject featureProject, CloneOccurence occurence)
	{
		if (featureProject == null || featureProject.getFeatureModel() == null)
			return;
		final IFile file = ResourcesPlugin.getWorkspace().getRoot()
				.getFileForLocation(occurence.getFile());
		final Feature feature = featureProject.getFeatureModel().getFeature(
				featureProject.getFeatureName(file));

		if (feature != null)
		{
			if (relevantFeatures == null)
				relevantFeatures = new HashSet<Feature>();

			relevantFeatures.add(feature);

			if (relevantFeatures != null)
			{
				if (relevantFeatures.size() > 1)
					cloneVariantType = CloneVariantType.CROSSFEATURE;
				else
					cloneVariantType = CloneVariantType.INTRAVARIANT;
			}
		}
	}

	private void checkForCrossProjectOccurences()
	{
		if (relevantProjects.size() > 1)
			cloneVariantType = CloneVariantType.CROSSPROJECT;
		else
			cloneVariantType = CloneVariantType.INTRAVARIANT;
	}

	/**
	 * @return the cloneVariantOccurence
	 */
	public CloneVariantType getCloneVariantType()
	{
		return cloneVariantType;
	}

	/**
	 * @return the relevantFeatures
	 */
	public Set<Feature> getRelevantFeatures()
	{
		return relevantFeatures;
	}
	
}
