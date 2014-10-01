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

import java.util.HashMap;
import java.util.LinkedList;

import javax.annotation.Nonnull;

/**
 * Represents a class at the {@link FSTModel}.<br>
 * Contains {@link FSTRole}s with their corresponding {@link FSTFeature}.
 * 
 * @author Jens Meinicke
 */
public class FSTClass {

	private final HashMap<String, FSTRole> roles = new HashMap<String, FSTRole>();
	private final String name;
	private LinkedList<String> invariants;

	public FSTClass(String name) {
		this.name = name;
		invariants = new LinkedList<String>();
	}

	public String getName() {
		return name;
	}

	@Nonnull
	public LinkedList<FSTRole> getRoles() {
		return new LinkedList<FSTRole>(roles.values());
	}

	public void addRole(String featureName, FSTRole role) {
		roles.put(featureName, role);
	}

	public FSTRole getRole(String featureName) {
		return roles.get(featureName);
	}

	public boolean hasInvariants() {
		return invariants.size() > 0;
	}

	public LinkedList<String> getInvariants() {
		return invariants;
	}

	@Override
	public String toString() {
		return name;
	}
	
}
