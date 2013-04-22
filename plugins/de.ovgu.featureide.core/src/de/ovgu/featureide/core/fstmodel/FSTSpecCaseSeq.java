/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.fstmodel;

/**
 * Representation of a Specification case sequence (contract) at a role.
 * 
 * @author Fabian Benduhn
 */
public class FSTSpecCaseSeq extends RoleElement {

	private boolean also;
	private boolean refines;

	/**
	 * @param methodName
	 * @param body
	 * @param beginLine
	 * @param endLine
	 * @param isAlso
	 */
	public FSTSpecCaseSeq(String methodName, String body, int beginLine,
			int endLine, boolean isAlso) {
		super(methodName, "contract", "", body, endLine, endLine);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.fstmodel.RoleElement#getFullName()
	 */
	@Override
	public String getFullName() {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * @param isAlso
	 */
	public void setAlso(boolean isAlso) {
		this.also = isAlso;

	}

	public boolean getAlso() {
		return this.also;
	}
	/**
	 * @param contains
	 */
	public void setRefines(boolean refines) {
		this.refines = refines;

	}

	/**
	 * @return
	 */
	public boolean refines() {
		return this.refines;
	}
}
