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

import java.util.TreeSet;

import javax.annotation.Nonnull;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;

/**
 * A role is a implementation unit representing a class at a corresponding
 * feature.
 * 
 * @author Jens Meinicke
 */
public class FSTRole {
	private final TreeSet<FSTDirective> directives = new TreeSet<FSTDirective>();
	private final FSTClassFragment classFragment;

	private FSTFeature feature;
	private FSTClass fstClass;
	private IFile file;

	public FSTRole(IFile file, FSTFeature feature, FSTClass fstClass) {
		this.feature = feature;
		this.fstClass = fstClass;
		this.file = file;
		this.classFragment = new FSTClassFragment(fstClass.getName());
		this.classFragment.setRole(this);
	}

	public void add(FSTDirective directive) {
		directives.add(directive);
		directive.setRole(this);
	}

	public FSTClass getFSTClass() {
		return fstClass;
	}

	public FSTFeature getFeature() {
		return feature;
	}

	public IFile getFile() {
		return file;
	}

	public void setFile(IFile file) {
		this.file = file;
	}

	public FSTClassFragment getClassFragment() {
		return classFragment;
	}

	@Nonnull
	public TreeSet<FSTDirective> getDirectives() {
		return directives;
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append(fstClass.getName());
		builder.append(" @ ");
		builder.append(feature.getName());
		builder.append("\n");
		for (FSTField f : classFragment.fields) {
			builder.append(f.getName());
			builder.append("\n");
		}
		for (FSTMethod m : classFragment.methods) {
			builder.append(m.getName());
			builder.append("\n");
		}
		return builder.toString();
	}
}