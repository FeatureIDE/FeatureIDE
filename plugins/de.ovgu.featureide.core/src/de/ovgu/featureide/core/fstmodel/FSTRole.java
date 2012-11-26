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

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;

/**
 * A role is a implementation unit representing a class at a corresponding feature.
 * 
 * @author Jens Meinicke
 */
public class FSTRole {

	private LinkedList<FSTMethod> methods;
	private LinkedList<FSTField> fields;
	private LinkedList<FSTDirective> directives;
	private IFile file;
	private FSTFeature feature;
	private FSTClass fstClass;

	public FSTRole(IFile file, FSTFeature feature, FSTClass fstClass) {
		this.feature = feature;
		this.fstClass = fstClass;
		this.file = file;
		methods = new LinkedList<FSTMethod>();
		fields = new LinkedList<FSTField>();
		directives = new LinkedList<FSTDirective>();
	}
	
	public LinkedList<FSTDirective> getDirectives() {
		return directives;
	}

	public void add(FSTDirective directive) {
		directives.add(directive);
		directive.setRole(this);
	}
	
	public void add(RoleElement element) {
		if (element instanceof FSTMethod) {
			for (FSTMethod m : methods) {
				if (m.getFullName().equals(element.getFullName())) {
//					CorePlugin.getDefault().logWarning("Model already contains method " 
//					+ element.getFullName() + " @ " + feature.getName()+ "/" + fstClass.getName());
					return;
				}
			}
			methods.add((FSTMethod) element);
		} else {
			for (FSTField f : fields) {
				if (f.getFullName().equals(element.getFullName())) {
//					CorePlugin.getDefault().logWarning("Model already contains method " 
//					+ element.getFullName() + " @ " + feature.getName()+ "/" + fstClass.getName());
					return;
				}
			}
			fields.add((FSTField) element);
		}
		element.setRole(this);
	}
	
	public FSTClass getFSTClass() {
		return fstClass;
	}

	public FSTFeature getFeture() {
		return feature;
	}

	public IFile getFile() {
		return file;
	}
	
	public void setFile(IFile file) {
		this.file = file;
	}

	public LinkedList<FSTField> getFields() {
		return fields;
	}

	public LinkedList<FSTMethod> getMethods() {
		return methods;
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append(fstClass.getName());
		builder.append(" @ ");
		builder.append(feature.getName());
		builder.append("\n");
		for (FSTField f : fields) {
			builder.append(f.getName());
			builder.append("\n");
		}
		for (FSTMethod m : methods) {
			builder.append(m.getName());
			builder.append("\n");
		}
		return builder.toString();
	}
}
