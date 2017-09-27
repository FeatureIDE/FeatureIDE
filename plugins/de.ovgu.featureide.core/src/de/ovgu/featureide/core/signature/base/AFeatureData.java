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
package de.ovgu.featureide.core.signature.base;

import org.prop4j.Node;

/**
 * Stores information about a {@link AbstractSignature} in a certain feature.</br> An instance of this class is stored in a signature instance for every feature
 * that implements the signature.
 *
 * @author Sebastian Krieter
 */
public abstract class AFeatureData implements IConstrainedObject {

	protected final int startLineNumber, endLineNumber;
	protected final int id;

	protected Node constraint;

	protected String comment;

	protected AFeatureData(int id, int lineNumber, int endLineNumber) {
		startLineNumber = lineNumber;
		this.endLineNumber = endLineNumber;
		this.id = id;
	}

	public int getStartLineNumber() {
		return startLineNumber;
	}

	public int getEndLineNumber() {
		return endLineNumber;
	}

	@Override
	public Node getConstraint() {
		return constraint;
	}

	public void setConstraint(Node constraint) {
		this.constraint = constraint;
	}

	public String getComment() {
		return comment;
	}

	public void setComment(String comment) {
		this.comment = comment;
	}

	public int getID() {
		return id;
	}

	public boolean hasID(int id) {
		return (this.id == -1) || (this.id == id);
	}

}
