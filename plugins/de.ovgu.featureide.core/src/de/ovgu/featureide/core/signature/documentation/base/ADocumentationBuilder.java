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
package de.ovgu.featureide.core.signature.documentation.base;

import java.util.List;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.filter.IFilter;

/**
 * Abstract documentation builder.
 * 
 * @author Sebastian Krieter
 */
public abstract class ADocumentationBuilder {
	
	private final IFeatureProject featureProject;
	
	public ADocumentationBuilder(IFeatureProject featureProject) {
		this.featureProject = featureProject;
	}
	
	public final void build(ADocumentationCommentMerger merger, List<IFilter<AbstractSignature>> filters) {
		final List<SignatureCommentPair> list = getCollector(featureProject).collect(filters);

		final ADocumentationCommentParser parser = getParser();
		
		for (SignatureCommentPair pair : list) {
			// parse
			parser.parse(pair.getComment());
			
			// merge
			merger.sortFeatureList(parser.getFeatureTags());
			final List<BlockTag> featureTags = merger.mergeList(parser.getFeatureTags());
			final List<BlockTag> generalTags = merger.mergeList(parser.getGeneralTags());
			
			setComment(pair.getSignature(), merger.mergeLists(generalTags, featureTags));
		}
	}

	protected abstract ADocumentationCommentCollector getCollector(IFeatureProject featureProject);
	protected abstract ADocumentationCommentParser getParser();
	
	protected abstract void setComment(AbstractSignature signature, String comment);
}
