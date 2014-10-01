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
package de.ovgu.featureide.featurehouse;

import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class SignatureSetter implements JobFinishListener {
	private FSTModel fstModel = null;
	private ProjectSignatures signatures = null;
	
	public void setFstModel(FSTModel fstModel) {
		this.fstModel = fstModel;
		if (signatures != null) {
			assignSignatures();
		}
	}
	
	public void setSignatures(ProjectSignatures signatures) {
		this.signatures = signatures;
		if (fstModel != null) {
			assignSignatures();
		}
	}
	
	private void assignSignatures() {
		fstModel.setProjectSignatures(signatures);
	}
	
	@Override
	public void jobFinished(boolean success) {
//		setSignatures(signatures);
	}
}
