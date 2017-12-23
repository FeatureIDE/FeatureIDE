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

import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringUtil;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiLocalVariableSignature;

/**
 * TODO description
 * 
 * @author steffen
 * @param <T>
 */
public abstract class SignatureMatcher {

	protected final ProjectSignatures signatures;
	protected final AbstractSignature selectedElement;
	protected AbstractSignature selectedSignature;
	protected final String newName;
	protected Set<AbstractSignature> newNameMatchedSignatures;
	private Set<AbstractSignature> matchedSignatures;
	protected Map<String, AbstractClassSignature> classes = new HashMap<>();

//	protected Set<AbstractSignature> subClasses = new HashSet<>();
//	protected Set<AbstractSignature> superClasses = new HashSet<>();
//	protected Set<AbstractSignature> interfaces = new HashSet<>();

	public SignatureMatcher(final ProjectSignatures signatures, final AbstractSignature selectedElement, final String newName) {
		this.signatures = signatures;
		this.selectedElement = selectedElement;
		this.newName = newName;
	}

	public void findMatchedSignatures() {
		classes = RefactoringUtil.getClasses(signatures);
		matchedSignatures = getNamedMatchedSignatures(selectedElement.getName());
		newNameMatchedSignatures = getNamedMatchedSignatures(newName);
		selectedSignature = selectSignature();
		matchedSignatures = determineMatchedSignatures();
	}

	protected abstract Set<AbstractSignature> determineMatchedSignatures();

	private AbstractSignature selectSignature() {
		if (selectedElement instanceof FujiLocalVariableSignature) return selectedElement;

		if (matchedSignatures.size() == 1) {
			return matchedSignatures.iterator().next();
		} else {
			for (AbstractSignature matchedSignature : matchedSignatures) {
				if (matchedSignature.equals(selectedElement)) return matchedSignature;
			}
		}
		return null;
	}

	protected Set<AbstractSignature> getNamedMatchedSignatures(final String name) {
		Set<AbstractSignature> matched = new HashSet<>();
		final SignatureIterator iter = signatures.iterator();
		while (iter.hasNext()) {
			final AbstractSignature signature = iter.next();
			if (checkSignature(signature, name)) {
				matched.add(signature);
			}
		}

		return matched;
	}

	protected abstract boolean hasSameType(final AbstractSignature signature);

	protected boolean checkSignature(final AbstractSignature signature, final String sigName) {
		return RefactoringUtil.hasSameName(signature, sigName) && hasSameType(signature);
	}

	public Set<AbstractSignature> getMatchedSignatures() {
		return matchedSignatures;
	}

	public AbstractSignature getSelectedSignature() {
		return selectedSignature;
	}

	public Set<AbstractSignature> getMatchedSignaturesForNewName() {
		return newNameMatchedSignatures;
	}

//	public AbstractMethodSignature findDeclaringMethod(AbstractMethodSignature overriding) throws JavaModelException {
//		AbstractMethodSignature result= null;
//		AbstractMethodSignature overridden= findOverriddenMethod(overriding);
//		while (overridden != null) {
//			result= overridden;
//			overridden= findOverriddenMethod(result);
//		}
//		return result;
//	}
//	
//	/**
//	 * Finds the method that is overridden by the given method.
//	 * First the super class is examined and then the implemented interfaces.
//	 * @param overriding the overriding method
//	 * @return a method that is directly overridden by the given method, or <code>null</code>
//	 */
//	public AbstractMethodSignature findOverriddenMethod(AbstractMethodSignature overriding) {
//		if (overriding.isPrivate() || overriding.isStatic() || overriding.isConstructor()) {
//			return null;
//		}
//
//		AbstractClassSignature type = overriding.getParent();
//		AbstractClassSignature superClass = getSuperclass(type);
//		if (superClass != null) {
//			AbstractMethodSignature res= findOverriddenMethodInHierarchy(superClass, overriding);
//			if (res != null) {
//				if (isVisibleInHierarchy(res, type.getPackage())) {
//					return res;
//				}
//			}
//		}
//		Set<AbstractClassSignature> interfaces = getSuperInterfaces(type);
//		for (AbstractClassSignature classInterface : interfaces) {
//			AbstractMethodSignature res= findOverriddenMethodInHierarchy(classInterface, overriding);
//			if (res != null) {
//				return res; // methods from interfaces are always public and therefore visible
//			}
//		}
//		return null;
//	}
//
//	private boolean isVisibleInHierarchy(final AbstractMethodSignature res, final String pack) {
//
//		final AbstractClassSignature parent = res.getParent();
//		if (parent == null) return false;
//
//		if (parent.isPublic() || parent.isProtected() || parent.getType().equals(ExtendedFujiSignaturesJob.TYPE_INTERFACE)) {
//			return true;
//		} else if (parent.isPrivate()) {
//			return false;
//		}
//
//		return (pack != null && pack.equals(parent.getPackage()));
//	}
//
//	private Set<AbstractClassSignature> getSuperInterfaces(AbstractClassSignature type) {
//		final Set<AbstractClassSignature> result = new HashSet<>();
//		final Set<String> implementList = type.getImplementList();
//		for (String implement : implementList) {
//			if (classes.containsKey(implement)) {
//				result.add(classes.get(implement));
//			}
//		}
//		return result;
//	}
//
//	private AbstractClassSignature getSuperclass(final AbstractClassSignature type) {
//		final HashSet<String> extendList = type.getExtendList();
//		if (extendList.size() == 1)
//			return classes.get(extendList.iterator().next());
//		
//		return null;
//	}
//
//	/**
//	 * Finds the directly overridden method in a type and its super types. First the super class is examined and then the implemented interfaces.
//	 * With generics it is possible that 2 methods in the same type are overidden at the same time. In that case, the first overridden method found is returned.
//	 * 	@param superClass The type to find methods in
//	 * @param overriding The overriding method
//	 * @return The first overridden method or <code>null</code> if no method is overridden
//	 * @throws JavaModelException if a problem occurs
//	 */
//	public AbstractMethodSignature findOverriddenMethodInHierarchy(AbstractClassSignature classSig, AbstractMethodSignature overriding) {
//		AbstractMethodSignature method= findOverriddenMethodInType(classSig, overriding);
//		if (method != null) {
//			return method;
//		}
//		AbstractClassSignature superClass= getSuperclass(classSig);
//		if (superClass != null) {
//			AbstractMethodSignature res=  findOverriddenMethodInHierarchy(superClass, overriding);
//			if (res != null) {
//				return res;
//			}
//		}
//		Set<AbstractClassSignature> superInterfaces = getSuperInterfaces(classSig);
//		for (AbstractClassSignature classInterface : superInterfaces) {
//			AbstractMethodSignature res= findOverriddenMethodInHierarchy(classInterface, overriding);
//			if (res != null) {
//				return res;
//			}
//		}
//		return method;
//	}
//
//	/**
//	 * Finds an overridden method in a type. With generics it is possible that 2 methods in the same type are overridden at the same time.
//	 * In that case the first overridden method found is returned.
//	 * @param superClass The type to find methods in
//	 * @param overriding The overriding method
//	 * @return The first overridden method or <code>null</code> if no method is overridden
//	 * @throws JavaModelException if a problem occurs
//	 */
//	public AbstractMethodSignature findOverriddenMethodInType(AbstractClassSignature superClass, AbstractMethodSignature overriding) {
//		if (overriding.isPrivate() || overriding.isStatic() || overriding.isConstructor())
//			return null;
//		
//		final Set<AbstractMethodSignature> overriddenMethods= superClass.getMethods();
//		for (AbstractMethodSignature overridden : overriddenMethods) {
//			if (overridden.isPrivate() || overridden.isStatic() || overridden.isConstructor())
//				continue;
//			if (RefactoringUtil.hasSameName(overriding, overridden) && overridden.getParameterTypes().equals(overriding.getParameterTypes())) {
//				return overridden;
//			}
//		}
//		return null;
//	}
//	
//	/**
//	 * Locates the topmost method of an override ripple and returns it. If none
//	 * is found, null is returned.
//	 *
//	 * @param method the IMethod which may be part of a ripple
//	 * @param typeHierarchy a ITypeHierarchy of the declaring type of the method. May be null
//	 * @param monitor an IProgressMonitor
//	 * @return the topmost method of the ripple, or null if none
//	 * @throws JavaModelException
//	 */
//	public AbstractMethodSignature getTopmostMethod(final AbstractMethodSignature method) throws JavaModelException {
//
//		Assert.isNotNull(method);
//
////		ITypeHierarchy hierarchy= typeHierarchy;
//		AbstractMethodSignature topmostMethod= null;
////		final AbstractClassSignature declaringType= method.getParent();
////		if (!declaringType.getType().equals(ExtendedFujiSignaturesJob.TYPE_INTERFACE)) {
////
////			AbstractMethodSignature inInterface= isDeclaredInInterface(method, hierarchy, monitor);
////			if (inInterface != null && !inInterface.equals(method))
////				topmostMethod= inInterface;
////		}
////		
//		if (topmostMethod == null) {
//			AbstractMethodSignature overrides= overridesAnotherMethod(method);
//			if (overrides != null && !overrides.equals(method))
//				topmostMethod= overrides;
//		}
//		return topmostMethod;
//	}
//	
//	public AbstractMethodSignature overridesAnotherMethod(final AbstractMethodSignature method) throws JavaModelException {
//		AbstractMethodSignature found = findDeclaringMethod(method);
//		boolean overrides= (found != null && !found.equals(method) && (!found.isStatic()) && (!found.isPrivate()));
//		if (overrides)
//			return found;
//		else
//			return null;
//	}
//
////	public AbstractMethodSignature isDeclaredInInterface(AbstractMethodSignature method) throws JavaModelException {
////		//Assert.isTrue(isVirtual(method));
////		for (AbstractSignature matchedSignature : matchedSignatures) {
////			
////		} 
////			for (int i= 0; i < classes.length; i++) {
////				final IType clazz= classes[i];
////				IType[] superinterfaces= null;
////				if (clazz.equals(hierarchy.getType()))
////					superinterfaces= hierarchy.getAllSuperInterfaces(clazz);
////				else
////					superinterfaces= clazz.newSupertypeHierarchy(new SubProgressMonitor(subMonitor, 1)).getAllSuperInterfaces(clazz);
////				for (int j= 0; j < superinterfaces.length; j++) {
////					IMethod found= Checks.findSimilarMethod(method, superinterfaces[j]);
////					if (found != null && !found.equals(method))
////						return found;
////				}
////			}
////			return null;
////		} finally {
////		}
////	}

}
