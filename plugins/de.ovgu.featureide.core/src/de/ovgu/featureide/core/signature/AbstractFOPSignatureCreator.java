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
package de.ovgu.featureide.core.signature;

import java.util.HashMap;
import java.util.List;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.core.signature.base.FeatureDataConstructor;

/**
 * Loads FOP Signatures
 * 
 * @author Reimar Schröter
 */
public abstract class AbstractFOPSignatureCreator {
	protected static final class SignatureReference {
		private final HashMap<Integer, FOPFeatureData> ids = new HashMap<>();
		private final AbstractSignature sig;

		public SignatureReference(AbstractSignature sig) {
			this.sig = sig;
		}

		public final FOPFeatureData[] getFeatureData() {
			FOPFeatureData[] ret = new FOPFeatureData[ids.size()];
			int i = -1;
			for (FOPFeatureData id : ids.values()) {
				ret[++i] = id;
			}
			return ret;
		}

		public final void addID(FOPFeatureData featureData) {
			if (!ids.containsKey(featureData.getID())) {
				ids.put(featureData.getID(), featureData);
			}
		}

		public final AbstractSignature getSig() {
			return sig;
		}
	}

	protected final HashMap<AbstractSignature, SignatureReference> signatureSet = new HashMap<AbstractSignature, SignatureReference>();
	protected final HashMap<String, AbstractSignature> signatureTable = new HashMap<String, AbstractSignature>();
	private FeatureDataConstructor featureDataConstructor = null;

	protected ProjectSignatures createSignatures(IFeatureProject fp) {
		ProjectSignatures projectSignatures = new ProjectSignatures(fp.getFeatureModel());
		featureDataConstructor = new FeatureDataConstructor(projectSignatures, FeatureDataConstructor.TYPE_FOP);
		return projectSignatures;
	}

	protected AbstractSignature addFeatureID(AbstractSignature sig, int featureID, int startLine, int endLine) {
		SignatureReference sigRef = signatureSet.get(sig);
		if (sigRef == null) {
			sigRef = new SignatureReference(sig);
			signatureSet.put(sig, sigRef);
			signatureTable.put(sig.getFullName(), sig);
		}
		sigRef.addID((FOPFeatureData) featureDataConstructor.create(featureID, startLine, endLine));
		return sigRef.getSig();
	}

	public class SimpleClassSignature extends AbstractClassSignature {

		public SimpleClassSignature(AbstractClassSignature parent, String name, String modifiers, String type, String pckg) {
			super(parent, name, modifiers, type, pckg);
		}

	}

	public class SimpleMethodSignature extends AbstractMethodSignature {

		public SimpleMethodSignature(AbstractClassSignature parent, String name, String modifier, String type, List<String> parameterTypes,
				boolean isConstructor) {
			super(parent, name, modifier, type, parameterTypes, isConstructor);
		}

		@Override
		public String getReturnType() {
			return type;
		}

	}

	public class SimpleFieldSignature extends AbstractFieldSignature {

		public SimpleFieldSignature(AbstractClassSignature parent, String name, String modifiers, String type) {
			super(parent, name, modifiers, type);
		}

	}

}
