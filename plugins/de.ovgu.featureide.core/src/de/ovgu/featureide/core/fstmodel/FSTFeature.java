/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.fstmodel;

import java.util.HashMap;
import java.util.LinkedList;

import javax.annotation.Nonnull;

/**
 * Represents a feature at the {@link FSTModel}.<br>
 * Contains {@link FSTRole}s with their corresponding {@link FSTClass}.
 * 
 * @author Jens Meinicke
 */
public class FSTFeature {

	HashMap<String, FSTRole> roles;
	String name;
	int color;

	public FSTFeature(String name) {
		this.name = name;
		roles = new HashMap<String, FSTRole>();
	}

	public void setColor(int color) {
		this.color = color;
	}
	
	public int getColor() {
		return color;
	}

	public String getName() {
		return name;
	}

	@Nonnull
	public LinkedList<FSTRole> getRoles() {
		 return new LinkedList<FSTRole>(roles.values());
	}

	public FSTRole getRole(String className) {
		return roles.get(className);
	}
}
