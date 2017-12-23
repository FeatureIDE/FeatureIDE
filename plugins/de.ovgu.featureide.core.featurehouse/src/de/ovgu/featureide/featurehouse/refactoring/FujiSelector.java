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
package de.ovgu.featureide.featurehouse.refactoring;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.ExtendedSignature;
import de.ovgu.featureide.core.signature.base.FOPFeatureData;
import de.ovgu.featureide.core.signature.base.SignaturePosition;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
public class FujiSelector {

	private final ProjectSignatures projectSignatures;
	private final String file;

	public FujiSelector(final IFeatureProject featureProject, final String file) {
		this.file = file;
		this.projectSignatures = featureProject.getProjectSignatures();
	}

	public AbstractSignature getSelectedSignature(int line, int column) {

		final SignatureIterator iter = projectSignatures.iterator();
		while (iter.hasNext()) {
			final AbstractSignature signature = iter.next();

			for (FOPFeatureData featureData : (FOPFeatureData[]) signature.getFeatureData()) {
				if (isSignatureSelected(featureData, featureData.getSigPosition(), line, column)) return signature;
			}

			for (ExtendedSignature invokedSig : signature.getInvocationSignatures()) {
				for (AFeatureData invokedFeatureData : invokedSig.getSig().getFeatureData()) {
					if (invokedFeatureData.getID() == invokedSig.getFeatureID()
						&& isSignatureSelected(invokedFeatureData, invokedSig.getPosition(), line, column)) {
						return signature;
					}
				}
			}
		}

		return null;
	}

	public FujiClassSignature getSelectedClassSignature() {

		final SignatureIterator iter = projectSignatures.iterator();
		while (iter.hasNext()) {
			final AbstractSignature signature = iter.next();

			if (!(signature instanceof FujiClassSignature)) continue;

			for (FOPFeatureData featureData : (FOPFeatureData[]) signature.getFeatureData()) {
				if (featureData.getAbsoluteFilePath().equals(file)) return (FujiClassSignature) signature;
			}

		}

		return null;
	}

	private boolean isSignatureSelected(AFeatureData featureData, SignaturePosition sigPosition, int line, int column) {
		return (featureData.getAbsoluteFilePath().equals(file)
			&& ((sigPosition.getStartRow() == line) && (sigPosition.getIdentifierStart() <= column) && (sigPosition.getIdentifierEnd() >= column)));
	}

}
