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
package de.ovgu.featureide.core.mpl.signature.documentation.base;

import java.util.Iterator;
import java.util.List;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.mpl.signature.documentation.BlockTag;

/**
 * Abstract documentation builder.
 * 
 * @author Sebastian Krieter
 */
public abstract class ADocumentationBuilder<T> {
	
	private final IFeatureProject featureProject;
	
	public ADocumentationBuilder(IFeatureProject featureProject) {
		this.featureProject = featureProject;
	}
	
	public final void build(ADocumentationCommentMerger merger) {
		final Iterator<SignatureCommentPair<T>> it = getCollector(featureProject).collect();

		final ADocumentationCommentParser parser = getParser();
		
		while (it.hasNext()) {
			SignatureCommentPair<T> pair = it.next();
			// parse
			parser.parse(pair.getComment());
			
			// merge
			final List<BlockTag> generalTags = merger.mergeList(parser.getGeneralTags());
			final List<BlockTag> featureTags = merger.mergeList(parser.getFeatureTags());
			
			setComment(pair.getSignature(), merger.mergeLists(generalTags, featureTags));
		}
	}

	protected abstract ADocumentationCommentCollector<T> getCollector(IFeatureProject featureProject);
	protected abstract ADocumentationCommentParser getParser();
	
	protected abstract void setComment(T signature, String comment);
}
