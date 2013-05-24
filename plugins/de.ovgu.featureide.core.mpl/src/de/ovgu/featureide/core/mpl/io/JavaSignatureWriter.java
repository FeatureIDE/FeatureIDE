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
import de.ovgu.featureide.core.mpl.signature.java.JavaFieldSignature;
import de.ovgu.featureide.core.mpl.signature.java.JavaMethodSignature;
import de.ovgu.featureide.core.mpl.signature.java.JavaRoleMap;
import de.ovgu.featureide.core.mpl.signature.java.JavaRoleSignature;

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
	
	public void writeSignatures() {
		JavaRoleMap roleMap = new JavaRoleMap(interfaceProject);
		interfaceProject.setRoleMap(roleMap);

		for (FSTFeature feature : fstmodel.getFeatures()) {
			for (FSTRole fstrole : feature.getRoles()) {
				String classname = fstrole.getName();
				if (fstrole.getName().endsWith(IOConstants.EXTENSION_JAVA)) {
					classname = classname.substring(0, classname.length() - IOConstants.EXTENSION_JAVA.length());
					
					JavaRoleSignature roleSig = new JavaRoleSignature(classname, fstrole.getModifiers(), 
							fstrole.getType(), fstrole.getPackage(), feature.getName());
					
					roleMap.addRole(roleSig);
					writeClass(roleSig, fstrole);
				}
			}
		}
	}
	
	private void writeClass(JavaRoleSignature classSig, FSTClassFragment classFragment) {
		String classname = classFragment.getName();
		
		if (classname.endsWith(IOConstants.EXTENSION_JAVA)) {
			classname = classname.substring(0, classname.length() - IOConstants.EXTENSION_JAVA.length());
		}
		
		for (String imp : classFragment.getImports()) {
			classSig.addImport(imp);
		}
		for (String extend : classFragment.getExtends()) {
			classSig.addExtend(extend);
		}
		for (String implement : classFragment.getImplements()) {
			classSig.addImplement(implement);
		}
		for (FSTField field : classFragment.getFields()) {
			classSig.addField(new JavaFieldSignature(field.getName(), 
					field.getModifiers(), field.getType()));
		}
		for (FSTMethod method : classFragment.getMethods()) {
			classSig.addMethod(new JavaMethodSignature(method.getName(), 
					method.getModifiers(), method.getType(),
					method.getParameter(), method.isConstructor(), false));
		}
		for (FSTClassFragment innerClass : classFragment.getInnerClasses()) {
			JavaRoleSignature innerClassSig =
				new JavaRoleSignature(innerClass.getName(), innerClass.getModifiers(), innerClass.getType(), null, null);
			classSig.addInnerClass(innerClassSig);
			writeClass(innerClassSig, innerClass);
		}
	}
}