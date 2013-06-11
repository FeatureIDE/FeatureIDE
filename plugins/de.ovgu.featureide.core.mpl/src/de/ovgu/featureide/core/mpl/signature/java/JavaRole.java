package de.ovgu.featureide.core.mpl.signature.java;

import de.ovgu.featureide.core.mpl.signature.ViewTag;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractRole;

public class JavaRole extends AbstractRole {
	
	public JavaRole(String featureName, JavaRoleSignature signature) {
		super(featureName, signature);
	}
	
	private JavaRole(JavaRole javaRole, ViewTag viewTag) {
		super(javaRole, viewTag);
	}

	@Override
	public String toString() {
		return JavaStringBuilder.getClassString(this, false);
	}

	@Override
	public String toShortString() {
		return JavaStringBuilder.getClassString(this, true);
	}

	@Override
	public JavaClass toClass() {
		return new JavaClass(signature);
	}

	@Override
	public JavaRole reduce(ViewTag viewTag) {
		return new JavaRole(this, viewTag);
	}
}
