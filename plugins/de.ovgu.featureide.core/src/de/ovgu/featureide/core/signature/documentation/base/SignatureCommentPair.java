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

import java.util.List;

import de.ovgu.featureide.core.signature.base.AbstractSignature;

public class SignatureCommentPair {

	public static class Comment {

		private final String comment;
		private final int featureID;

		public Comment(String comment, int featureID) {
			this.comment = comment;
			this.featureID = featureID;
		}

		public int getFeatureID() {
			return featureID;
		}

		public String getComment() {
			return comment;
		}
	}

	private final AbstractSignature signature;
	private final List<Comment> comment;

	public SignatureCommentPair(AbstractSignature signature, List<Comment> comment) {
		super();
		this.signature = signature;
		this.comment = comment;
	}

	public AbstractSignature getSignature() {
		return signature;
	}

	public List<Comment> getComment() {
		return comment;
	}

}
