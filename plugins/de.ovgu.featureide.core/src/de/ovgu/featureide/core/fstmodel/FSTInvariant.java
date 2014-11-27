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
 * description
 * 
 * @author Stefan Krueger
 * @author Florian Proksch
 */
public class FSTInvariant extends RoleElement<FSTInvariant> {

	public enum RoleTypes {
		ROLE_TYPE_INVARIANT, MISC
	}

	RoleTypes parentRoleType;

	/**
	 * @param name name of the invariant
	 * @param body content of the invariant
	 */
	public FSTInvariant(String name, String body) {
		super(name, "", "", body, -1, -1);
	}

	/**
	 * @param name name of the invariant
	 * @param body content of the invariant
	 * @param beginLine first line of the invariant
	 * @param endLine last line of the invariant
	 */

	public FSTInvariant(String name, String body, int beginLine, int endLine) {
		super(name, "", "", body, beginLine, endLine);
	}

	public int getUniqueIdentifier() {
		return (body + beginLine).hashCode();
	}

	public String getFullName() {
		String name = body.replaceAll("  ", "").replace((char) 10, ' ').replaceFirst("invariant\\W+", "").replaceFirst("invariant_redundantly\\W+", "");
		return ((name.length() > 25 ? name.substring(0, 25) + "..." : name));
	}

	public boolean inRefinementGroup() {
		for (FSTRole role : getRole().getFSTClass().getRoles()) {
			if (role.getFeature().equals(getRole().getFeature())) {
				continue;
			}
			for (FSTInvariant invariant : role.getClassFragment().getInvariants()) {
				if (invariant.getName().equals(getName())) {
					return true;
				}
			}
		}
		return false;
	}

	public boolean equals(Object obj) {
		if (!(obj instanceof FSTInvariant))
			return false;
		return ((FSTInvariant) obj).getUniqueIdentifier() == getUniqueIdentifier();
	}
}
