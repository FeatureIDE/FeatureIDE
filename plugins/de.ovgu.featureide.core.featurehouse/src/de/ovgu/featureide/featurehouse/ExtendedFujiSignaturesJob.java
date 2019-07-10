/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Loads the signatures from Fuji.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public class ExtendedFujiSignaturesJob implements LongRunningMethod<ProjectSignatures> {

	public static final class SignatureMethodAccess {

		private final int featureID;
		private final AbstractSignature absSig;

		public int getFeatureID() {
			return featureID;
		}

		public AbstractSignature getAbsSig() {
			return absSig;
		}

		@Override
		public boolean equals(Object arg0) {
			if (arg0 == this) {
				return true;
			}
			if (!(arg0 instanceof SignatureMethodAccess)) {
				return false;
			}
			final SignatureMethodAccess comp = (SignatureMethodAccess) arg0;
			if ((featureID != comp.featureID) || !absSig.equals(comp.absSig)) {
				return false;
			}
			return true;
		}

		@Override
		public int hashCode() {
			int hashCode = featureID;
			hashCode = (37 * hashCode) + absSig.hashCode();
			return hashCode;
		}

		@Override
		public String toString() {
			return featureID + "; " + absSig.toString();
		}

		public SignatureMethodAccess(int featureID, AbstractSignature absSig) {
			this.featureID = featureID;
			this.absSig = absSig;
		}
	}

	private final IFeatureProject featureProject;
	private final ProjectSignatures projectSignatures;

	public ProjectSignatures getProjectSignatures() {
		return projectSignatures;
	}

	public ExtendedFujiSignaturesJob(IFeatureProject featureProject) {
		this.featureProject = featureProject;
		projectSignatures = new ProjectSignatures(this.featureProject.getFeatureModel());
	}

	@Override
	public ProjectSignatures execute(IMonitor monitor) throws Exception {
		throw new UnsupportedOperationException("Fuji is currently not supported.");
	}

}
