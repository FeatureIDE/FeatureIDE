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
package de.ovgu.featureide.core.fstmodel;

/**
 * Representation of a method at a role.
 *
 * @author Jens Meinicke
 */
public class FSTField extends RoleElement<FSTField> {

	public FSTField(String name, String type, String modifiers) {
		this(name, type, modifiers, "", -1, -1);
	}

	public FSTField(String fieldName, String typeName, String modifiers, String body, int beginLine, int endLine) {
		super(fieldName, typeName, modifiers, body, beginLine, endLine);
	}

	@Override
	public String getFullName() {
		return name + " : " + type;
	}

	public boolean inRefinementGroup() {
		for (final FSTRole role : getRole().getFSTClass().getRoles()) {
			if (role.getFeature().equals(getRole().getFeature())) {
				continue;
			}
			for (final FSTField field : role.getClassFragment().getFields()) {
				if (field.getName().equals(getName())) {
					return true;
				}
			}
		}
		return false;
	}

}
