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

import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.documentation.base.SignatureCommentPair.Comment;

/**
 * Abstract merger for modul-comment.
 *
 * @author Sebastian Krieter
 */
class DocumentationCommentCollector {

	public static List<SignatureCommentPair> collect(ProjectSignatures projectSignatures) {
		final SignatureIterator it = projectSignatures.iterator();

		final List<SignatureCommentPair> list = new LinkedList<>();

		while (it.hasNext()) {
			final AbstractSignature curSignature = it.next();
			final AFeatureData[] featureDataArray = curSignature.getFeatureData();
			final List<Comment> commentList = new LinkedList<>();

			for (int j = 0; j < featureDataArray.length; j++) {
				final AFeatureData featureData = featureDataArray[j];
				if (featureData.getComment() != null) {
					commentList.add(new Comment(featureData.getComment(), featureData.getID()));
				}
			}
			list.add(new SignatureCommentPair(curSignature, commentList));
		}

		return list;
	}

}
