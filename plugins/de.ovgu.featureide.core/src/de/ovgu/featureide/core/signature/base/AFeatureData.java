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
package de.ovgu.featureide.core.signature.base;

import java.util.Arrays;


/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public abstract class AFeatureData {
		protected final int lineNumber;
		
		protected int[] ids;
		protected String comment;
		
		public AFeatureData(int id, int lineNumber) {
			this.lineNumber = lineNumber;
			this.ids = new int[]{id};
		}
		
		public AFeatureData(int lineNumber) {
			this.lineNumber = lineNumber;
		}
		
		public AFeatureData(int[] ids, int lineNumber) {
			this.lineNumber = lineNumber;
			setIDs(ids);
		}
		
		public int getLineNumber() {
			return lineNumber;
		}
		
		public String getComment() {
			return comment;
		}

		public void setComment(String comment) {
			this.comment = comment;
		}
		
		public void setIDs(int[] ids) {
			this.ids = ids;
			Arrays.sort(ids);
		}

		public int[] getIDs() {
			return ids;
		}
		
		public boolean hasID(int id) {
			return Arrays.binarySearch(ids, id) > -1;
		}
}
