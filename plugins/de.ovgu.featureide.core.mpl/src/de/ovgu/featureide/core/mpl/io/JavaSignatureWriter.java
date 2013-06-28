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
package de.ovgu.featureide.core.mpl.io;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtension;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.mpl.JavaInterfaceProject;
import de.ovgu.featureide.core.mpl.io.constants.IOConstants;
import de.ovgu.featureide.core.mpl.signature.RoleMap;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;
import de.ovgu.featureide.core.mpl.signature.java.JavaFieldSignature;
import de.ovgu.featureide.core.mpl.signature.java.JavaMethodSignature;
import de.ovgu.featureide.core.mpl.signature.java.JavaRole;
import de.ovgu.featureide.core.mpl.signature.java.JavaClassSignature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Saves information from the {@link FSTModel}.
 * 
 * @author Sebastian Krieter
 */
public class JavaSignatureWriter extends AbstractWriter {	
	
	private final FSTModel fstmodel;

	public JavaSignatureWriter(IFeatureProject sourceProject, JavaInterfaceProject interfaceProject) {
		super(interfaceProject);
		FSTModel fstmodel = sourceProject.getFSTModel();
		if (fstmodel == null) {
			IComposerExtension composer = sourceProject.getComposer();
			composer.initialize(sourceProject);
			composer.buildFSTModel();
			fstmodel = sourceProject.getFSTModel();
		}
		this.fstmodel = fstmodel;
	}
	
	public RoleMap writeSignatures() {
		RoleMap roleMap = new RoleMap(interfaceProject);

		for (FSTFeature feature : fstmodel.getFeatures()) {
			String featureName = feature.getName();
			for (FSTRole fstrole : feature.getRoles()) {
				String className = fstrole.getName();
				if (fstrole.getName().endsWith(IOConstants.EXTENSION_JAVA)) {
					className = className.substring(0, className.length() - IOConstants.EXTENSION_JAVA.length());
					
					JavaRole role = getRole(roleMap, featureName, null, className, 
							fstrole.getPackage(), fstrole);
					
					roleMap.addRole(role);
				}
			}
		}
		return roleMap;
	}
	
	public RoleMap writeSignatures(FeatureModel model) {
		RoleMap roleMap = new RoleMap(model);

		for (FSTFeature feature : fstmodel.getFeatures()) {
			String featureName = feature.getName();
			for (FSTRole fstrole : feature.getRoles()) {
				String className = fstrole.getName();
				if (fstrole.getName().endsWith(IOConstants.EXTENSION_JAVA)) {
					className = className.substring(0, className.length() - IOConstants.EXTENSION_JAVA.length());
					
					JavaRole role = getRole(roleMap, featureName, null, className, 
							fstrole.getPackage(), fstrole);
					
					roleMap.addRole(role);
				}
			}
		}
		return roleMap;
	}
	
	private JavaRole getRole(RoleMap roleMap, String featureName, AbstractClassSignature parent, String name, String pckg, FSTClassFragment classFragment) {		
		JavaClassSignature newRoleSig = new JavaClassSignature(null, name, classFragment.getModifiers(), classFragment.getType(), pckg);
		
		for (String extend : classFragment.getExtends()) {
			newRoleSig.addExtend(extend);
		}
		for (String implement : classFragment.getImplements()) {
			newRoleSig.addImplement(implement);
		}
		
		JavaClassSignature aSig = (JavaClassSignature) roleMap.getSignatureRef(newRoleSig);
		aSig.addFeature(featureName);
		
		for (String imp : classFragment.getImports()) {
			aSig.addImport(imp);
		}
		
		JavaRole newRole = new JavaRole(featureName, aSig);
		writeRole(roleMap, newRole, classFragment, featureName);
		
		return newRole;
	}
	
	private void writeRole(RoleMap roleMap, JavaRole role, FSTClassFragment classFragment, String featureName) {
		for (FSTField field : classFragment.getFields()) {
			JavaFieldSignature aSig = (JavaFieldSignature) roleMap.getSignatureRef(
					new JavaFieldSignature(role.getSignature(), field.getName(),
							field.getModifiers(), field.getType()));
			aSig.addFeature(featureName);
			
			role.addMember(aSig);
		}
		for (FSTMethod method : classFragment.getMethods()) {
			JavaMethodSignature aSig = (JavaMethodSignature) roleMap.getSignatureRef(
					new JavaMethodSignature(role.getSignature(), method.getName(),
							method.getModifiers(), method.getType(),
							method.getParameter(), method.isConstructor()));
			aSig.addFeature(featureName);
			
			role.addMember(aSig);
		}
		for (FSTClassFragment innerClass : classFragment.getInnerClasses()) {			
			JavaRole innerRole = getRole(roleMap, featureName, role.getSignature(), innerClass.getName(), 
					null, innerClass);
			
			role.addInnerClass(innerRole);
		}
	}
	

}