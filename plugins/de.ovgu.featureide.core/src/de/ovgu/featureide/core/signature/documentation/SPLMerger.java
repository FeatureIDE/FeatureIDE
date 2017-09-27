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
package de.ovgu.featureide.core.signature.documentation;

import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentMerger;
import de.ovgu.featureide.core.signature.documentation.base.BlockTag;
import de.ovgu.featureide.fm.core.filter.base.IFilter;

/**
 * Modul-Comment merger for SPLs.
 *
 * @author Sebastian Krieter
 */
public class SPLMerger extends ADocumentationCommentMerger {

	private static final long serialVersionUID = -7089505215805435500L;

	private static final class BlockTagFilter implements IFilter<BlockTag> {

		@Override
		public boolean isValid(BlockTag blockTag) {
			return blockTag.isFeatureIndependent(); // || blockTag.getPriority() > 0; // ???
		}
	}

	public SPLMerger() {
		addFilter(new BlockTagFilter());
	}

	@Override
	protected BlockTag adaptBlockTag(BlockTag tag) {
		if (tag.isFeatureSpecific() && (tag.getTagtype() != BlockTag.TAG_SEE)) {
			tag.setDesc("<b>[" + tag.getConstraint() + "]</b> " + tag.getDesc());
		}
		return tag;
	}

}
