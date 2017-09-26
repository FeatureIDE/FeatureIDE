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

import java.util.LinkedList;
import java.util.TreeSet;

import javax.annotation.Nonnull;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;

/**
 * A role is a implementation unit representing a class at a corresponding feature.
 *
 * @author Jens Meinicke
 * @author Dominic Labsch
 * @author Daniel P�sche
 */
public class FSTRole {

	private final TreeSet<FSTDirective> directives = new TreeSet<FSTDirective>();
	private final FSTClassFragment classFragment;

	private final FSTFeature feature;
	private final FSTClass fstClass;
	private IFile file;

	public FSTRole(IFile file, FSTFeature feature, FSTClass fstClass) {
		this.feature = feature;
		this.fstClass = fstClass;
		this.file = file;
		classFragment = new FSTClassFragment(fstClass.getName());
		classFragment.setRole(this);
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
	public TreeSet<FSTField> getFields() {
		return classFragment.getFields();
	}

	@Nonnull
	public TreeSet<FSTInvariant> getInvariants() {
		return classFragment.getInvariants();
	}

	@Nonnull
	public TreeSet<FSTMethod> getMethods() {
		return classFragment.getMethods();
	}

	@Nonnull
	public TreeSet<FSTClassFragment> getInnerClasses() {
		return classFragment.getInnerClasses();
	}

	@Nonnull
	public TreeSet<FSTDirective> getDirectives() {
		return directives;
	}

	// get all fields of all nested classes
	public LinkedList<FSTField> getAllFields() {
		final LinkedList<FSTField> allFields = new LinkedList<FSTField>();
		getAllFieldsRec(allFields, getClassFragment());
		return allFields;

	}

	private void getAllFieldsRec(LinkedList<FSTField> fields, FSTClassFragment innerClass) {
		fields.addAll(innerClass.getFields());
		for (final FSTClassFragment i : innerClass.getInnerClasses()) {
			getAllFieldsRec(fields, i);
		}
	}

	// get all methods of all nested classes
	public LinkedList<FSTMethod> getAllMethods() {
		final LinkedList<FSTMethod> allMethods = new LinkedList<FSTMethod>();
		getAllMethodsRec(allMethods, getClassFragment());
		return allMethods;

	}

	private void getAllMethodsRec(LinkedList<FSTMethod> methods, FSTClassFragment innerClass) {
		methods.addAll(innerClass.getMethods());
		for (final FSTClassFragment i : innerClass.getInnerClasses()) {
			getAllMethodsRec(methods, i);
		}

	}

	// get all nested classes of all nested classes
	public LinkedList<FSTClassFragment> getAllInnerClasses() {
		final LinkedList<FSTClassFragment> allInnerClasses = new LinkedList<FSTClassFragment>();
		getAllInnerClassesRec(allInnerClasses, getClassFragment());
		return allInnerClasses;

	}

	private void getAllInnerClassesRec(LinkedList<FSTClassFragment> fragment, FSTClassFragment innerClass) {
		fragment.addAll(innerClass.getInnerClasses());
		for (final FSTClassFragment i : innerClass.getInnerClasses()) {
			getAllInnerClassesRec(fragment, i);
		}
	}

	// get list of all nested classes shared by multiple features
	public LinkedList<FSTClassFragment> getAllEqualFSTFragments(FSTClassFragment fragment) {
		final LinkedList<FSTClassFragment> frag = new LinkedList<FSTClassFragment>();

		for (final FSTRole role : fstClass.getRoles()) {
			for (final FSTClassFragment currFrag : role.getAllInnerClasses()) {
				if (currFrag.equals(fragment)) {
					frag.add(currFrag);
					break;
				}
			}
		}

		return frag;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append(fstClass.getName());
		builder.append(" @ ");
		builder.append(feature.getName());
		builder.append("\n");
		for (final FSTField f : classFragment.fields) {
			builder.append(f.getName());
			builder.append("\n");
		}
		for (final FSTMethod m : classFragment.methods) {
			builder.append(m.getName());
			builder.append("\n");
		}
		return builder.toString();
	}
}
