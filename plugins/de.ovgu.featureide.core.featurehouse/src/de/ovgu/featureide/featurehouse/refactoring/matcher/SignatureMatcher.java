/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.refactoring.matcher;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.eclipse.jdt.core.IMember;

import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringSignature;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringUtil;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;


/**
 * TODO description
 * 
 * @author steffen
 * @param <T>
 */
public abstract class SignatureMatcher {

	private final ProjectSignatures signatures;
	protected final IMember selectedElement;
	protected AbstractSignature selectedSignature;
	private final String newName;
	private Set<AbstractSignature> newMatchedSignatures;
	protected Set<AbstractSignature> oldMatchedSignatures;
	protected Map<String, AbstractClassSignature> classes = new HashMap<>();
	
	protected Set<AbstractSignature> subClasses = new HashSet<>();
	protected Set<AbstractSignature> superClasses = new HashSet<>();
	protected Set<AbstractSignature> interfaces = new HashSet<>();


	public SignatureMatcher(final ProjectSignatures signatures, final IMember selectedElement, final String newName) {
		this.signatures = signatures;
		this.selectedElement = selectedElement;
		this.newName = newName;
	}
	
	public void findMatchedSignatures(){
		classes = getClasses();
		oldMatchedSignatures = getNamedMatchedSignatures(selectedElement.getElementName());
		newMatchedSignatures = getNamedMatchedSignatures(newName); 
		selectedSignature = selectSignature();
		
		final Set<AbstractClassSignature> involvedClasses = new HashSet<>();
		
		if (selectedSignature instanceof FujiClassSignature) {
			involvedClasses.add((FujiClassSignature) selectedSignature);
		}
		else {
			involvedClasses.add(selectedSignature.getParent());
		}
		
		addInvolvedClasses(involvedClasses);
	}
	
	protected abstract void addInvolvedClasses(final Set<AbstractClassSignature> involvedClasses);
	
	private AbstractSignature selectSignature() {
		if (oldMatchedSignatures.size() == 1) {
			return oldMatchedSignatures.iterator().next();
		} else {
			for (AbstractSignature matchedSignature : oldMatchedSignatures) {
				if (checkSignature(matchedSignature) && RefactoringUtil.hasSameClass(matchedSignature, selectedElement))
					return matchedSignature;
			}
		}
		return null;
	}
	
	
	
	private Map<String, AbstractClassSignature> getClasses() {
		final Map<String, AbstractClassSignature> classes = new HashMap<>();

		final SignatureIterator iter = signatures.iterator();
		while (iter.hasNext()) {
			final AbstractSignature signature = iter.next();
			if (signature instanceof AbstractClassSignature)
				classes.put(signature.getName(), (AbstractClassSignature) signature);
		}

		return classes;
	}
	
	
	private Set<AbstractSignature> getNamedMatchedSignatures(final String name) {
		Set<AbstractSignature> matched = new HashSet<>();
		final SignatureIterator iter = signatures.iterator();
		while (iter.hasNext()) {
			final AbstractSignature signature = iter.next();
			if (RefactoringUtil.hasSameName(signature, name) && hasSameType(signature)) {
				matched.add(signature);
			}
		}

		return matched;
	}
	
	
	protected abstract boolean hasSameType(AbstractSignature signature);
	protected abstract boolean checkSignature(AbstractSignature signature);
	
	public abstract Set<AbstractSignature> getMatchedSignatures();
	
	public AbstractSignature getSelectedSignature()
	{
		return selectedSignature;
	}

}
