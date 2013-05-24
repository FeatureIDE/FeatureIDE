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
import java.util.Iterator;
import java.util.LinkedList;

import de.ovgu.featureide.core.mpl.signature.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.ViewTag;

/** 
 * Holds the java signature of a role (class).
 * 
 * @author Sebastian Krieter
 * @author Reimar Schroeter
 */
public class JavaRoleSignature extends AbstractClassSignature<JavaRoleSignature> {
	private final String featureName;
	
	public JavaRoleSignature(String name, String modifiers, String type, String pckg, String featureName, LinkedList<ViewTag> tags) {
		super(name, modifiers, type, pckg, tags, false);
		this.featureName = featureName;
		
		fields = new LinkedList<JavaFieldSignature>();
		methods = new LinkedList<JavaMethodSignature>();
		innerClasses = new HashMap<String, JavaRoleSignature>();
		importList = new LinkedList<String>();
		extendList = new LinkedList<String>();
		implementList = new LinkedList<String>();
	}
	
	public JavaRoleSignature(String name, String modifiers, String type, String pckg, String featureName) {
		this(name, modifiers, type, pckg, featureName, null);
	}
	
	private JavaRoleSignature(JavaRoleSignature curJavaRole, ViewTag viewTag, boolean ext) {
		super(curJavaRole.name, curJavaRole.modifiers, curJavaRole.type, curJavaRole.pckg, curJavaRole.viewTags, ext || curJavaRole.ext);
		featureName = curJavaRole.featureName;
		
		fields = new LinkedList<JavaFieldSignature>();
		methods = new LinkedList<JavaMethodSignature>();
		innerClasses = new HashMap<String, JavaRoleSignature>();
		
		for (JavaFieldSignature curField : curJavaRole.fields) {
			if(curField.hasViewTag(viewTag)){
				fields.add(new JavaFieldSignature(curField));
			}
		}		
		for (JavaMethodSignature curMethod : curJavaRole.methods) {
			if(curMethod.hasViewTag(viewTag)){
				methods.add(new JavaMethodSignature(curMethod));
			}
		}
		for (JavaRoleSignature innerRole : curJavaRole.getInnerClasses().values()) {
			if(innerRole.hasViewTag(viewTag)) {
				innerClasses.put(innerRole.getFullName(), new JavaRoleSignature(innerRole, viewTag, ext));
			}
		}
		
		importList = new LinkedList<String>(curJavaRole.getImportList());
		extendList = new LinkedList<String>(curJavaRole.getExtendList());
		implementList = new LinkedList<String>(curJavaRole.getImplementList());
	}
	
	public JavaRoleSignature(JavaRoleSignature curJavaRole, ViewTag viewTag) {
		this(curJavaRole, viewTag, false);
	}
	
	public JavaRoleSignature(JavaRoleSignature curJavaRole) {
		this(curJavaRole, null, false);
	}

	public JavaClassSignature toJavaClass() {		
		return new JavaClassSignature(name, modifiers, type, pckg, viewTags, ext);
	}
	
	public String getFeatureName() {
		return featureName;
	}

	public LinkedList<String> getImportList() {
		return (LinkedList<String>) importList;
	}

	public LinkedList<String> getExtendList() {
		return (LinkedList<String>) extendList;
	}

	public LinkedList<String> getImplementList() {
		return (LinkedList<String>) implementList;
	}

	@Override
	public void clearViewTags() {
		super.clearViewTags();
		for (JavaFieldSignature field : fields) {
			field.clearViewTags();
		}
		for (JavaMethodSignature method : methods) {
			method.clearViewTags();
		}
	}
	
	public static Object[] intersectionOfJavaRoleSignature(LinkedList<JavaRoleSignature> signatureList, JavaRoleSignature unionRole){
		boolean somethingAdded = false;
		
		//Methoden
		HashMap<String, LinkedList<JavaMethodSignature>> methodSignaturesEqualNames = new HashMap<String, LinkedList<JavaMethodSignature>>();
		for (Iterator<JavaRoleSignature> classRole = signatureList.iterator(); classRole.hasNext();) {
			JavaRoleSignature javaRoleSignature = classRole.next();
			for (Iterator<JavaMethodSignature> methIt = javaRoleSignature.methods.iterator(); methIt.hasNext();) {
				JavaMethodSignature javaMethodSignature = methIt.next();
				if(methodSignaturesEqualNames.containsKey(javaMethodSignature.getName())){
					methodSignaturesEqualNames.get(javaMethodSignature.getName()).add(javaMethodSignature);
				}else{
					LinkedList<JavaMethodSignature> list = new LinkedList<JavaMethodSignature>();
					list.add(javaMethodSignature);
					methodSignaturesEqualNames.put(javaMethodSignature.getName(), list);
				}
				
			}	
		}
		
		for (Iterator<String> methodIt = methodSignaturesEqualNames.keySet().iterator(); methodIt.hasNext();) {
			String methName = methodIt.next();
			LinkedList<JavaMethodSignature> tmpMethList = methodSignaturesEqualNames.get(methName);
			if(tmpMethList.size() < signatureList.size()){
				//Rolle kann nicht übernommen werden
			}else{
				//neue Rolle für Result erstellen
				if(tmpMethList.size()>0){
					int hash = tmpMethList.get(0).hashCode();
					for (Iterator<JavaMethodSignature> iterator = tmpMethList.iterator(); iterator.hasNext();) {
						JavaMethodSignature javaMethodSignature = iterator.next();
						if(hash != javaMethodSignature.hashCode())
							break; break;
					}
					
					JavaMethodSignature tmp = tmpMethList.get(0);
					//existiert Method in parent?
					if(!unionRole.getMethods().contains(tmp)){
						JavaMethodSignature addSig = new JavaMethodSignature(tmp.getName(), tmp.getModifiers(), tmp.getType(), tmp.getParameterTypes(), tmp.isConstructor(), true);
						//TODO  Tags....
//						addSig.addViewTag("view1", 1);
						unionRole.addMethod(addSig);
						somethingAdded = true;
					}
				}
			}
		}
		
		//Felder
		HashMap<String, LinkedList<JavaFieldSignature>> fieldSignaturesEqualNames = new HashMap<String, LinkedList<JavaFieldSignature>>();
		for (JavaRoleSignature javaRoleSignature : signatureList) {
			for (JavaFieldSignature javaFieldSignature : javaRoleSignature.fields) {
				if(fieldSignaturesEqualNames.containsKey(javaFieldSignature.getName())){
					fieldSignaturesEqualNames.get(javaFieldSignature.getName()).add(javaFieldSignature);
				}else{
					LinkedList<JavaFieldSignature> list = new LinkedList<JavaFieldSignature>();
					list.add(javaFieldSignature);
					fieldSignaturesEqualNames.put(javaFieldSignature.getName(), list);
				}
			}	
		}
		
		
		for (String fieldName : fieldSignaturesEqualNames.keySet()) {
			LinkedList<JavaFieldSignature> tmpFieldList = fieldSignaturesEqualNames.get(fieldName);
			if(tmpFieldList.size() < signatureList.size()){
				//Rolle kann nicht übernommen werden
			}else{
				//neue Rolle für Result erstellen
				if(tmpFieldList.size() > 0){
					int hash = tmpFieldList.get(0).hashCode();
					for (JavaFieldSignature tmpField : tmpFieldList) {
						if(hash != tmpField.hashCode())
							break; break;
					}
					JavaFieldSignature tmp = tmpFieldList.get(0);
					//existiert Method in parent?
					if(!unionRole.getFields().contains(tmp)){
						JavaFieldSignature addSig = tmp.createExtendedSignature();
						//TODO  Tags....
//						addSig.addViewTag("view1", 1);
						unionRole.addField(addSig);
						somethingAdded = true;
					}
				}
			}
		}
		return new Object[]{unionRole, somethingAdded}; 
	}
	
	@Override
	public JavaRoleSignature createExtendedSignature() {
		return new JavaRoleSignature(this, null, true);
	}
}
