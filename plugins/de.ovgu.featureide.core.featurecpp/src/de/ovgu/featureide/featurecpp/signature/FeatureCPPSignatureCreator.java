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
package de.ovgu.featureide.featurecpp.signature;

import java.util.ArrayList;
import java.util.LinkedList;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.signature.AbstractFOPSignatureCreator;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AbstractSignature;

/**
 * Loads signatures of FeatureC++ projects using the FSTModel
 * 
 * @author Reimar Schröter
 */
public class FeatureCPPSignatureCreator extends AbstractFOPSignatureCreator {

	public ProjectSignatures createSignatures(IFeatureProject fp) {
		ProjectSignatures projectSignatures = super.createSignatures(fp);

		createSigs(fp, projectSignatures);
		final AbstractSignature[] sigArray = new AbstractSignature[signatureSet.size()];
		int i = -1;

		for (SignatureReference sigRef : signatureSet.values()) {
			AbstractSignature sig = sigRef.getSig();
			sig.setFeatureData(sigRef.getFeatureData());
			sigArray[++i] = sig;
		}

		projectSignatures.setSignatureArray(sigArray);
		return projectSignatures;
	}

	private ArrayList<AbstractSignature> createSigs(IFeatureProject fp, ProjectSignatures projectSignatures) {
		final ArrayList<AbstractSignature> signatureList = new ArrayList<>();

		FSTModel model = fp.getFSTModel();
		for (FSTClass curClass : model.getClasses()) {
			LinkedList<FSTRole> roles = curClass.getRoles();
			for (FSTRole fstRole : roles) {
				String featurename = fstRole.getFeature().getName();

				SimpleClassSignature classSig = (SimpleClassSignature) addFeatureID(new SimpleClassSignature(null, curClass.getName().replace(".h", ""), "",
						null, ""), projectSignatures.getFeatureID(featurename), 0, 0);
				FSTClassFragment classFragment = fstRole.getClassFragment();

				for (FSTMethod fstMethod : classFragment.getMethods()) {
					addFeatureID(
							new SimpleMethodSignature(classSig, fstMethod.getName(), fstMethod.getModifiers(), fstMethod.getType(), fstMethod.getParameter(),
									fstMethod.isConstructor()), projectSignatures.getFeatureID(featurename), fstMethod.getLine(), fstMethod.getEndLine());
				}

				for (FSTField field : classFragment.getFields()) {
					addFeatureID(new SimpleFieldSignature(classSig, field.getName(), field.getModifiers(), field.getType()),
							projectSignatures.getFeatureID(featurename), field.getLine(), field.getLine());
				}
			}

		}
		return signatureList;
	}

}
