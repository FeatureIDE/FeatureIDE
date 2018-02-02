package de.ovgu.featureide.cloneanalysis.results;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.jfree.chart.ChartFactory;
import org.jfree.chart.ChartUtilities;
import org.jfree.chart.JFreeChart;
import org.jfree.chart.plot.PlotOrientation;
import org.jfree.data.statistics.HistogramDataset;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;

public class CloneAnalysisGraphResults {

	public static void createGraphsForResults(CloneAnalysisResults<VariantAwareClone> results, String outputFolder,
			Set<FeatureRootLocation> relevantFeatures) {
		createGraphsForResults(results, new Path(outputFolder), relevantFeatures);
	}

	private static void createGraphsForResults(CloneAnalysisResults<VariantAwareClone> results, IPath path,
			Set<FeatureRootLocation> relevantFeatures) {

		Map<Integer, Set<VariantAwareClone>> clonesByFeatureCount = new HashMap<Integer, Set<VariantAwareClone>>();
		for (VariantAwareClone clone : results.getClones()) {
			final int featureCount = featureCount(results, clone);
			if (clonesByFeatureCount.get(featureCount) == null)
				clonesByFeatureCount.put(featureCount, new HashSet<VariantAwareClone>());

			clonesByFeatureCount.get(featureCount).add(clone);
		}
		for (int i = 1; i <= results.getRelevantFeatures().size(); i++) {
			if (clonesByFeatureCount.get(i) != null)
				plotCloneCountOverCloneLength(i, clonesByFeatureCount.get(i), path);
		}

	}

	private static void plotCloneCountOverCloneLength(int featureCount, Set<VariantAwareClone> clonesByFeatureCount,
			IPath path) {
		String title = "Length of clones with occurences in " + featureCount + " features";
		HistogramDataset data = new HistogramDataset();

		int maxLength = 0, i = 0;
		double[] series = new double[clonesByFeatureCount.size()];

		for (Clone clone : clonesByFeatureCount) {
			if (clone.getLineCount() > maxLength)
				maxLength = clone.getLineCount();
			series[i++] = clone.getLineCount();
		}

		data.addSeries("Clones", series, maxLength);

		// JFreeChart histogram = ChartFactory.createHistogram(title, "Lines of
		// Code", "Clones", data,
		// PlotOrientation.VERTICAL, false, false, false);
		JFreeChart histogram = ChartFactory.createHistogram("", "Length (in LOC)", "Clones", data,
				PlotOrientation.VERTICAL, false, false, false);

		try {
			/**
			 * This utility saves the JFreeChart as a JPEG First Parameter:
			 * FileName Second Parameter: Chart To Save Third Parameter: Height
			 * Of Picture Fourth Parameter: Width Of Picture
			 */

			ChartUtilities.saveChartAsJPEG(new File(path.append("Histogram" + featureCount).toString() + ".jpeg"),
					histogram, 800, 600);
		} catch (IOException e) {
			e.printStackTrace();
			System.err.println("Problem occurred saving chart.");
		}
	}

	private static int featureCount(CloneAnalysisResults<VariantAwareClone> results, VariantAwareClone clone) {
		int count = 0;
		for (FeatureRootLocation feature : results.getRelevantFeatures())
			for (CloneOccurence occurence : clone.getOccurences())
				if (feature.getLocation().isPrefixOf(occurence.getFile())) {
					count++;
					break;
				}

		assert count <= results.getRelevantFeatures().size() : "Clone cannot be part of more features than there are";
		return count;
	}

}
