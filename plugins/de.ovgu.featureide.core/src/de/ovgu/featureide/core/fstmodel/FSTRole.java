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

import java.util.HashSet;
import java.util.LinkedList;

import javax.annotation.Nonnull;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;

/**
 * A role is a implementation unit representing a class at a corresponding feature.
 * 
 * @author Jens Meinicke
 */
public class FSTRole {

	private LinkedList<FSTMethod> methods = new LinkedList<FSTMethod>();
	private LinkedList<FSTField> fields = new LinkedList<FSTField>();
	private LinkedList<FSTDirective> directives = new LinkedList<FSTDirective>();
	private LinkedList<FSTSpecCaseSeq> contracts = new LinkedList<FSTSpecCaseSeq>();
	private IFile file;
	private FSTFeature feature;
	private FSTClass fstClass;
	
	private final HashSet<String> 
		importList = new HashSet<String>(),
		extendList = new HashSet<String>(),
		implementList = new HashSet<String>();
		
	public FSTRole(IFile file, FSTFeature feature, FSTClass fstClass) {
		this.feature = feature;
		this.fstClass = fstClass;
		this.file = file;
	}

	public void add(FSTDirective directive) {
		directives.add(directive);
		directive.setRole(this);
	}
	
	public void add(RoleElement element) {
		if (element instanceof FSTMethod) {
			for (FSTMethod m : methods) {
				if (m.comparesTo(element)) {
//					CorePlugin.getDefault().logWarning("Model already contains method " 
//					+ element.getFullName() + " @ " + feature.getName()+ "/" + fstClass.getName());
					return;
				}
			}
			methods.add((FSTMethod) element);
		} else if (element instanceof FSTField){
			for (FSTField f : fields) {
				if (f.comparesTo(element)) {
//					CorePlugin.getDefault().logWarning("Model already contains method " 
//					+ element.getFullName() + " @ " + feature.getName()+ "/" + fstClass.getName());
					return;
				}
			}
			fields.add((FSTField) element);
		} else if(element instanceof FSTSpecCaseSeq){
			contracts.add((FSTSpecCaseSeq) element);
		}
		element.setRole(this);
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

	@Nonnull
	public LinkedList<FSTField> getFields() {
		return fields;
	}

	@Nonnull
	public LinkedList<FSTMethod> getMethods() {
		return methods;
	}
	
	@Nonnull
	public LinkedList<FSTDirective> getDirectives() {
		return directives;
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
	
	/**
	 * @return
	 */
	public LinkedList<FSTSpecCaseSeq> getContracts() {
		return contracts;
	}
	
	public void addImport(String imp) {
		importList.add(imp);
	}
	
	public void addImplement(String implement) {
		implementList.add(implement);
	}

	public void addExtend(String extend) {
		extendList.add(extend);
	}
	
	/**
	 * will only be set if using 
	 * the FeatureHouseComposer
	 */
	public HashSet<String> getImports() {
		return importList;
	}
	
	/**
	 * will only be set if using 
	 * the FeatureHouseComposer
	 */
	public HashSet<String> getExtends() {
		return extendList;
	}
	
	/**
	 * will only be set if using 
	 * the FeatureHouseComposer
	 */
	public HashSet<String> getImplements() {
		return implementList;
	}
}
