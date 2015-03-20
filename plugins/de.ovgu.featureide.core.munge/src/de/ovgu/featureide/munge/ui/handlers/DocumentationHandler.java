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
package de.ovgu.featureide.munge.ui.handlers;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.job.PrintDocumentationJob;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.documentation.VariantMerger;
import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentMerger;
import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentParser;
import de.ovgu.featureide.core.signature.filter.FeatureFilter;
import de.ovgu.featureide.core.signature.filter.IFilter;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationReader;
import de.ovgu.featureide.munge.MungeCorePlugin;
import de.ovgu.featureide.munge.documentation.DocumentationCommentParser;
import de.ovgu.featureide.ui.handlers.base.AFeatureProjectHandler;

public class DocumentationHandler extends AFeatureProjectHandler {
	
	@Override
	protected void singleAction(IFeatureProject featureProject) {
		final ADocumentationCommentParser parser = new DocumentationCommentParser();
		final List<IFilter<AbstractSignature>> filters = new LinkedList<>();
		
		final ProjectSignatures projectSignatures = featureProject.getProjectSignatures();
		if (projectSignatures == null) {
			CorePlugin.getDefault().logWarning("No signatures available!");
			return;
		}
			
		int[] featureIDs = projectSignatures.getFeatureIDs();
		
		final Configuration conf = new Configuration(featureProject.getFeatureModel(),
		Configuration.PARAM_LAZY | Configuration.PARAM_IGNOREABSTRACT);
		try {
			IFile file = featureProject.getCurrentConfiguration();
			new ConfigurationReader(conf).readFromFile(file);
		} catch (Exception e) {
			MungeCorePlugin.getDefault().logError(e);
			return;
		}
		final List<Feature> featureSet = conf.getSelectedFeatures();
		
		final int[] tempFeatureList = new int[featureSet.size()];
		int count = 0;
		for (Feature selctedFeature : featureSet) {
			final int id = projectSignatures.getFeatureID(selctedFeature.getName());
			if (id >= 0) {
				tempFeatureList[count++] = id;
			}
		}
		final int[] featureList = new int[count];
		
		// sort feature list
		int c = 0;
		for (int j = 0; j < featureIDs.length; j++) {
			int curId = featureIDs[j];
			for (int k = 0; k < count; k++) {
				if (curId == tempFeatureList[k]) {
					featureList[c++] = curId;
					break;
				}
			}
		}
		
		filters.add(new FeatureFilter(featureList));
		
		final ADocumentationCommentMerger merger = new VariantMerger(featureIDs.length, featureList);
		
		final PrintDocumentationJob.Arguments args =
				new PrintDocumentationJob.Arguments("doc", new String[0], parser, merger, filters);
		
		List<IProject> pl = new LinkedList<>();
		pl.add(featureProject.getProject());
		
		FMCorePlugin.getDefault().startJobs(pl, args, true);
	}
	
}
