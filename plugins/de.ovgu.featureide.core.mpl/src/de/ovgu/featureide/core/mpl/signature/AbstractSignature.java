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
package de.ovgu.featureide.core.mpl.signature;

import java.util.Iterator;
import java.util.LinkedList;

/** 
 * Abstract signature for class member.
 * 
 * @author Sebastian Krieter
 */
public abstract class AbstractSignature {
	protected static final String LINE_SEPARATOR = System.getProperty("line.separator");
	
	protected final String name;
	protected final String modifiers;
	protected final String type;
	
	protected final boolean ext;
	
	protected LinkedList<ViewTag> viewTags;
	
	protected AbstractSignature(String name, String modifiers, String type, LinkedList<ViewTag> viewTags, boolean ext) {
		this.name = name;
		
		if (modifiers == null) {
			this.modifiers = "";
		} else {
			this.modifiers = modifiers.trim();
		}
		if (type == null) {
			this.type = "";
		} else {
			this.type = type;
		}
		this.viewTags = viewTags; 
		this.ext = ext;
	}
	
	public abstract AbstractSignature createExtendedSignature();
	
	public boolean hasViewTag(ViewTag viewTag) {
		if (viewTag == null) {
			return true;
		}
		if (viewTags != null) {
			for (ViewTag vt : viewTags) {
				if (vt.matches(viewTag)) {
					return true;
				}
			}
		}
		return false;
	}
	
	public void addViewTag(ViewTag viewTag) {
		if (viewTags == null) {
			viewTags = new LinkedList<ViewTag>();
		}
		viewTags.add(viewTag);
	}
	
	public void clearViewTags() {
		viewTags = null;
	}
	
	public void deleteViewTag(String name) {
		if (viewTags != null) {
			Iterator<ViewTag> it = viewTags.iterator();
			while (it.hasNext()) {
				if (it.next().getName().equals(name)) {
					it.remove();
				}
			}
		}
	}

	public String getName() {
		return name;
	}
	
	public String getModifiers() {
		return modifiers;
	}
	
	public String getType() {
		return type;
	}

	@Override
	public boolean equals(Object obj) {
		AbstractSignature otherSig = (AbstractSignature) obj;
		if (!type.equals(otherSig.type)) {
			return false;
		}
		if (!name.equals(otherSig.name)) {
			return false;
		}
		if (!modifiers.equals(otherSig.modifiers)) {
			return false;
		}
		return true;
	}
}
