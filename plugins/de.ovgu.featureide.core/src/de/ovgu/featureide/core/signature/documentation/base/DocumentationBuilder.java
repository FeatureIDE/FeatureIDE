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
package de.ovgu.featureide.core.signature.documentation.base;

import java.util.Collection;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.fm.core.filter.base.IFilter;

/**
 * Abstract documentation builder.
 *
 * @author Sebastian Krieter
 */
public class DocumentationBuilder {

	private final ADocumentationCommentParser parser;
	private final IFeatureProject featureProject;

	public DocumentationBuilder(IFeatureProject featureProject) {
		this.featureProject = featureProject;
		parser = featureProject.getComposer().getComposerObjectInstance(ADocumentationCommentParser.class);
	}

	public final void build(ADocumentationCommentMerger merger, Collection<IFilter<?>> filters) {
		final FSTModel fstModel = featureProject.getFSTModel();
		if (fstModel != null) {
			final ProjectSignatures projectSignatures = fstModel.getProjectSignatures();
			if (projectSignatures != null) {
				if (parser.addExtraFilters()) {
					for (final IFilter<?> filter : filters) {
						merger.addFilter(filter);
					}
				}
				for (final SignatureCommentPair pair : DocumentationCommentCollector.collect(projectSignatures)) {
					// parse
					parser.parse(projectSignatures, pair.getComment());
					// merge
					pair.getSignature().setMergedjavaDocComment(merger.merge(parser.getGeneralTags(), parser.getFeatureTags()));
				}
			} else {
				CorePlugin.getDefault().logWarning("No sigantures found for project '" + featureProject.getProjectName() + "'.");
			}
		}
	}

}
