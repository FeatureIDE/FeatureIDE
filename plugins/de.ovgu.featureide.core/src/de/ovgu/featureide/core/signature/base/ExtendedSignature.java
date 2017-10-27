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

/**
 * TODO description
 * 
 * @author steffen
 */
public class ExtendedSignature {

	private final AbstractSignature sig;
	private final int featureID;
	private final SignaturePosition position;

	public ExtendedSignature(AbstractSignature sig, int featureID, SignaturePosition position) {
		this.sig = sig;
		this.featureID = featureID;
		this.position = position;
	}

	@Override
	public int hashCode() {
		return (37 * featureID) + sig.hashCode() + position.hashCode();
	}

	@Override
	public boolean equals(Object arg0) {
		if (arg0 == this) {
			return true;
		}
		if (!(arg0 instanceof ExtendedSignature)) {
			return false;
		}
		ExtendedSignature comp = (ExtendedSignature) arg0;
		if (comp.featureID == this.featureID && comp.sig.equals(this.sig)) {
			return true;
		}

		if (comp.getPosition().getStartRow() == this.position.getStartRow() && comp.getPosition().getEndRow() == this.position.getEndRow()
			&& comp.getPosition().getIdentifierStart() == this.position.getIdentifierStart()
			&& comp.getPosition().getIdentifierEnd() == this.position.getIdentifierEnd()) return true;

		return false;
	}

	@Override
	public String toString() {
		return this.featureID + " - " + this.sig.getFullName();
	}

	public SignaturePosition getPosition() {
		return position;
	}

	public AbstractSignature getSig() {
		return sig;
	}

	public int getFeatureID() {
		return featureID;
	}
}
