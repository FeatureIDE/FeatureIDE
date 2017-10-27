package de.ovgu.featureide.cloneanalysis.results;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import net.sourceforge.pmd.cpd.Match;
import net.sourceforge.pmd.cpd.TokenEntry;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.utils.CloneAnalysisUtils;

/**
 * CPD is optimized for speed and badly documented, which sadly results in badly
 * formatted results.
 * 
 * This class handles the conversion of CPDs results into a better format.
 * 
 * @see CloneAnalysisResults
 * @see Clone
 * 
 * @author Konstantin Tonscheidt
 * 
 */
public class CPDResultConverter {

	/**
	 * Creates an Instance of {@link CloneAnalysisResults} and fills it with
	 * information gained from the matches found by CPD.
	 * 
	 * @param matchesFound
	 * @return
	 */
	public static CloneAnalysisResults<VariantAwareClone> convertMatchesToReadableResults(
			Iterator<Match> matchesFound) {
		Set<VariantAwareClone> clones = new HashSet<VariantAwareClone>();
		while (matchesFound.hasNext()) {
			final VariantAwareClone clone = convertMatchToClone(matchesFound.next());
			clones.add(clone);
		}

		CloneAnalysisResults<VariantAwareClone> results = new CloneAnalysisResults<VariantAwareClone>(clones);

		Set<FeatureRootLocation> relevantFeatures = CloneAnalysisUtils.getRelevantFeatures(results);

		results.setRelevantFeatures(relevantFeatures);
		results.setPercentageData(calculateClonedAmountPercentage(results));

		return results;
	}

	private static IClonePercentageData calculateClonedAmountPercentage(
			CloneAnalysisResults<VariantAwareClone> results) {
		ClonePercentageData clonePercentageData = new ClonePercentageData();
		final Set<FeatureRootLocation> relevantFeatures = results.getRelevantFeatures();
		final Map<FeatureRootLocation, Map<IFile, short[]>> featureClonedLinesPerFile = new HashMap<FeatureRootLocation, Map<IFile, short[]>>();

		for (FeatureRootLocation feature : relevantFeatures) {
			clonePercentageData.setFeatureTotalLineCount(feature,
					CloneAnalysisUtils.getMemberLineSum(feature.getLocation()));
			clonePercentageData.setFeatureTotalCloneLength(feature,
					CloneAnalysisUtils.getClonedLineCount(feature, results.getClones()));
			featureClonedLinesPerFile.put(feature, CloneAnalysisUtils.getEmptyMemberLinesMap(feature));
		}
		CloneAnalysisUtils.calculateClonedLines(featureClonedLinesPerFile, relevantFeatures, results);
		clonePercentageData.setFeatureClonedLinesPerFile(featureClonedLinesPerFile);

		return clonePercentageData;
	}

	/**
	 * Convenience Function calling {@link #checkForIntervariance(Set)}.
	 * 
	 * @see #checkForIntervariance(Set)
	 */
	public static boolean checkForIntervariance(Clone clone) {
		return checkForIntervariance(clone.getOccurences());
	}

	/**
	 * Checks the clones occurences. If occurences exist in different projects
	 * or, in the case of FeatureProjects, in different feature folders, the
	 * clone is intervariant.
	 * 
	 * @param occurences
	 *            the complete Set of the clones occurences.
	 * @return true if the clone is intervariant, false else.
	 */
	public static boolean checkForIntervariance(Set<CloneOccurence> occurences) {
		return false;
	}

	/**
	 * Creates a {@link Clone} object and fills it with information taken from
	 * the given {@link Match}.
	 * 
	 * @see Clone
	 * @see Match
	 */
	public static VariantAwareClone convertMatchToClone(Match match) {
		final int cloneLineCount = match.getLineCount();
		final int tokenCount = match.getTokenCount();
		final Set<CloneOccurence> occurences = new HashSet<CloneOccurence>();
		final Set<TokenEntry> tokens = match.getMarkSet();

		// System.out.println("Printing tokens");
		// System.out.println(match.getSourceCodeSlice());
		for (TokenEntry token : tokens) {
			if (token.getTokenSrcID() == null || token.getTokenSrcID().isEmpty()) {
				System.out.println("empty sourceid");
				continue;
			}
			CloneOccurence snippet = new CloneOccurence(token.getTokenSrcID(), token.getBeginLine());
			occurences.add(snippet);
		}

		final int fileCount = countFiles(occurences);

		final VariantAwareClone variantAwareClone = new VariantAwareClone(occurences, cloneLineCount, tokenCount,
				fileCount, match.getSourceCodeSlice());

		for (CloneOccurence occurence : variantAwareClone.getOccurences())
			occurence.setClone(variantAwareClone);

		return variantAwareClone;

	}

	/**
	 * @return the number of different files in which the Snippet occurs.
	 */
	public static int countFiles(Set<CloneOccurence> occurences) {
		Set<IPath> files = new HashSet<IPath>();
		for (CloneOccurence snippet : occurences)
			files.add(snippet.getFile());

		final int count = files.size();

		assert count > 0 : "Must be contained in one file at least.";

		return count;
	}

}
