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
package de.ovgu.featureide.core.mpl.signature.java;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

import de.ovgu.featureide.fm.core.Feature;

/**
 * Contains the {@link JavaRoleSignature}s for a feature.
 * 
 * @author Reimar Schroeter
 * @author Sebastian Krieter
 */
public class JavaFeatureSignature extends LinkedList<JavaRoleSignature> {
	private static final long serialVersionUID = 1L;
//	private Feature feature;
	
	public JavaFeatureSignature(Feature feature) {
//		this.feature = feature;
	}
	
	public JavaRoleSignature getJavaRoleSignature(String className) {
		for (JavaRoleSignature curRole : this) {
			if (curRole.getName().equals(className)) {
				return curRole;
			}
		}
		return null;
	}
	
	public static boolean intersectionOfJavaFeatureSignature(LinkedList<JavaFeatureSignature> featureList, JavaFeatureSignature unionFeature){
		boolean somethingAdded = false;
		
		HashMap<String, LinkedList<JavaRoleSignature>> rolesOfChildrens = sortedRoles(featureList);
		
		//Auswertung
		for (Iterator<String> classNameIt = rolesOfChildrens.keySet().iterator(); classNameIt.hasNext();) {
			String className = classNameIt.next();
			LinkedList<JavaRoleSignature> tmpClassLists = rolesOfChildrens.get(className);
			if(tmpClassLists.size() < featureList.size()){
				//Rolle kann nicht übernommen werden
			}else{
				//neue Rolle für Result erstellen
				//existiertRolle schon im "Parent"
				JavaRoleSignature parentRole = unionFeature.getJavaRoleSignature(className);
				if(parentRole == null){
					//komplett neu erstellen
					if(tmpClassLists.size() > 0){
						somethingAdded = true;
						JavaRoleSignature tmpRole = tmpClassLists.get(0);
						parentRole = tmpRole.createExtendedSignature();
						//TODO viewTag 
//						parentRole.addViewTag("view1", 1);
					}
				}
				
				Object[] res = JavaRoleSignature.intersectionOfJavaRoleSignature(tmpClassLists, parentRole);
				JavaRoleSignature newSig = (JavaRoleSignature) res[0];
				if((Boolean) res[1]){
					somethingAdded = true;
				}
				unionFeature.add(newSig);
			}
		}
		return somethingAdded;
	}
	
	public static boolean copyFromOnetoX(JavaFeatureSignature parent, LinkedList<JavaFeatureSignature> children){
		boolean somethingAdded = false;
		
		//gehe über alle felder/methoden aller Rollen....
		for (JavaRoleSignature javaRoleSignature : parent) {
			String classNameOfRole = javaRoleSignature.getName();
			
			for (JavaFeatureSignature curFeatureSig : children) {
				JavaRoleSignature curRole =curFeatureSig.getJavaRoleSignature(classNameOfRole);
			
				if(curRole == null) {
//					curRole = createNewEmptyRole(javaRoleSignature, curFeatureSig.getFeature().getName());
					curRole = (JavaRoleSignature) javaRoleSignature.createExtendedSignature();
//					curRole.addViewTag("view1",3);
					curFeatureSig.add(curRole);
					somethingAdded = true;
				}
				
				//Methoden
				for (JavaMethodSignature javaMethodSignature : javaRoleSignature.getMethods()) {
					if(!curRole.getMethods().contains(javaMethodSignature)){
						JavaMethodSignature tmpMethod = new JavaMethodSignature(javaMethodSignature.getName(), javaMethodSignature.getModifiers(), javaMethodSignature.getType(), javaMethodSignature.getParameterTypes(), javaMethodSignature.isConstructor(), true);
						//TODO viewTag
//						tmpMethod.addViewTag("view1",1);
						curRole.getMethods().add(tmpMethod);
						somethingAdded = true;
					}else{
						//TODO ... wenn zwei Views gemerged werden müssen
					}
				}
				
				//Felder
				for (JavaFieldSignature javaFieldSignature : javaRoleSignature.getFields()) {
					if(!curRole.getFields().contains(javaFieldSignature)){
						JavaFieldSignature tmpField = javaFieldSignature.createExtendedSignature();
//						tmpField.addViewTag("view1",1);
						curRole.addField(tmpField);
						somethingAdded = true;
					}
				}
			}
		}
		return somethingAdded;
	}
	
	public static boolean unionOfJavaFeatureSignature(LinkedList<JavaFeatureSignature> featureList){
		HashMap<String, LinkedList<JavaRoleSignature>> rolesOfChildrens = sortedRoles(featureList);
		boolean somethingAdded = false;
		
		//Auswertung
//		for (Iterator<String> classNameIt = rolesOfChildrens.keySet().iterator(); classNameIt.hasNext();) {
//			String className = classNameIt.next();
		for (String className : rolesOfChildrens.keySet()) {
			LinkedList<JavaRoleSignature> sameClassList = rolesOfChildrens.get(className);
			//alle Methoden aller Rollen holen
			
			HashSet<JavaMethodSignature> allMethods = new HashSet<JavaMethodSignature>();
			HashSet<JavaFieldSignature> allFields = new HashSet<JavaFieldSignature>();
			
			for (JavaRoleSignature curClass : sameClassList) {
				for (JavaMethodSignature curMethod : curClass.getMethods()) {
					if(!allMethods.contains(curMethod)){
						allMethods.add(curMethod);
					}
				}
				for (JavaFieldSignature curField : curClass.getFields()) {
					if(!allFields.contains(curField)){
						allFields.add(curField);
					}
				}
			}
			
			if(sameClassList.size() != featureList.size()){
				//TODO Klasse muss mit allen Methoden und Feldern neu erstellt werden
				//Adden der neuen Klassen... dann kann auch Methode "normal hinzugefügt werden"
				LinkedList<JavaRoleSignature> newClasses = new LinkedList<JavaRoleSignature>();
				for (JavaFeatureSignature curFeatureSig : featureList) {
					if(curFeatureSig.getJavaRoleSignature(sameClassList.get(0).getName()) == null){
						somethingAdded = true;
						JavaRoleSignature tmp = sameClassList.get(0);
						JavaRoleSignature newRole = tmp.createExtendedSignature();
						//TODO viewTag
//						newRole.addViewTag("view1",3);
						newClasses.add(newRole);
						curFeatureSig.add(newRole);
					}
				}
				sameClassList.addAll(newClasses);
			}
			for (JavaRoleSignature curClass : sameClassList) {
				for (JavaMethodSignature curMethod : allMethods) {
					if(!curClass.getMethods().contains(curMethod)){
						somethingAdded = true;
						JavaMethodSignature tmpMethod = new JavaMethodSignature(curMethod.getName(), curMethod.getModifiers(), curMethod.getType(), curMethod.getParameterTypes(), curMethod.isConstructor(), true);
						//TODO viewTag
//						tmpMethod.addViewTag("view1",1);
						curClass.getMethods().add(tmpMethod);
					}
				}
				
				for (JavaFieldSignature curField : allFields) {
					if(!curClass.getFields().contains(curField)){
						somethingAdded = true;
						JavaFieldSignature tmpField = curField.createExtendedSignature();
						//TODO viewTag
//						tmpField.addViewTag("view1",1);
						curClass.addField(tmpField);
					}
				}
			}

		}
		
		return somethingAdded;
	}
	
	private static HashMap<String, LinkedList<JavaRoleSignature>> sortedRoles(
			LinkedList<JavaFeatureSignature> featureList) {
		//Sortieren der Classes nach Namen
		HashMap<String, LinkedList<JavaRoleSignature>> rolesOfChildrens = new HashMap<String, LinkedList<JavaRoleSignature>>();
		
		for (JavaFeatureSignature javaFeatureSignature : featureList) {
			for (JavaRoleSignature javaRoleSignature : javaFeatureSignature) {
				String className = javaRoleSignature.getName();
				LinkedList<JavaRoleSignature> list = rolesOfChildrens.get(className);
				if (list == null) {
					list = new LinkedList<JavaRoleSignature>();
					rolesOfChildrens.put(className, list);
				}
				list.add(javaRoleSignature);
			}
		}
		return rolesOfChildrens;
	}

}
