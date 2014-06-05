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
 * Represents a feature at the {@link FSTModel}.<br>
 * Contains {@link FSTRole}s with their corresponding {@link FSTClass}.
 * 
 * @author Jens Meinicke
 */
public class FSTFeature {

	private final HashMap<String, FSTRole> roles = new HashMap<String, FSTRole>();
	protected String name;
	private int color = -1;
	private final FSTModel model;

	public FSTFeature(String name, final FSTModel model) {
		this.name = name;
		this.model = model;
	}
	
	public boolean isSelected() {
		FSTConfiguration config = model.getConfiguration();
		if (config != null) {
			return config.getSelectedFeatures().contains(name);
		}
		return false;
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
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return name;
	}

	/**
	 * @param className
	 * @param role
	 */
	public void addRole(String className, FSTRole role) {
		roles.put(className, role);
	}
}
