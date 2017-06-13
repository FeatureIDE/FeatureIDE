/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis.cnf;

import java.util.Arrays;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import de.ovgu.featureide.fm.core.analysis.cnf.manipulator.remove.CNFSlicer;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.CNFType;
import de.ovgu.featureide.fm.core.editing.AdvancedNodeCreator.ModelType;
import de.ovgu.featureide.fm.core.filter.AbstractFeatureFilter;
import de.ovgu.featureide.fm.core.filter.HiddenFeatureFilter;
import de.ovgu.featureide.fm.core.filter.base.IFilter;
import de.ovgu.featureide.fm.core.filter.base.OrFilter;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * 
 * @author Sebastian Krieter
 */
public class FeatureModelFormula {

	private static final int numberOfSlicedCNFs = 5;

	private final CNF[] slicedCNFs = new CNF[numberOfSlicedCNFs];
	private final Lock[] slicingLocks = new Lock[numberOfSlicedCNFs];
	{
		for (int i = 0; i < slicingLocks.length; i++) {
			slicingLocks[i] = new ReentrantLock();
		}
	}

	private final Lock cnfLock = new ReentrantLock();
	private final IFeatureModel featureModel;

	private FeatureModelCNF cnf;

	public FeatureModelFormula(IFeatureModel featureModel) {
		this.featureModel = featureModel.clone();
	}

	public IFeatureModel getFeatureModel() {
		return featureModel;
	}

	public FeatureModelCNF getCNF() {
		cnfLock.lock();
		try {
			if (cnf == null) {
				cnf = new FeatureModelCNF(featureModel, false);
				cnf.addClauses(Nodes.convert(cnf.getVariables(), AdvancedNodeCreator.createRegularCNF(featureModel)));
			}
			return cnf;
		} finally {
			cnfLock.unlock();
		}
	}

	public CNF getSlicedCNF(int index) {
		final FeatureModelCNF cnf2 = getCNF();
		final Lock slicingLock = slicingLocks[index];
		slicingLock.lock();
		try {
			CNF slicedCNF = slicedCNFs[index];
			if (slicedCNF == null) {
				final IFilter<IFeature> filter;
				switch (index) {
				case 0:
					filter = new AbstractFeatureFilter();
					break;
				case 1:
					filter = new HiddenFeatureFilter();
					break;
				case 2:
					filter = new OrFilter<IFeature>(Arrays.asList(new HiddenFeatureFilter(), new AbstractFeatureFilter()));
					break;
				default:
					return cnf2;
				}
				final CNFSlicer slicer = new CNFSlicer(cnf2, Functional.mapToList(featureModel.getFeatures(), filter, FeatureUtils.GET_FEATURE_NAME));
				slicedCNF = LongRunningWrapper.runMethod(slicer);
				slicedCNFs[index] = slicedCNF;
			}
			return slicedCNF;
		} finally {
			slicingLock.unlock();
		}
	}

	public void resetCNF() {
		cnfLock.lock();
		try {
			cnf = null;
		} finally {
			cnfLock.unlock();
		}
		for (int i = 0; i < slicedCNFs.length; i++) {
			final Lock slicingLock = slicingLocks[i];
			slicingLock.lock();
			try {
				slicedCNFs[i] = null;
			} finally {
				slicingLock.unlock();
			}
		}
	}

	//	// TODO use in FeatureProject
	//	@Override
	//	public void propertyChange(FeatureIDEEvent event) {
	//		switch (event.getEventType()) {
	//		// TODO !!!
	//		case MODEL_DATA_LOADED:
	//			resetCNF();
	//			break;
	//		default:
	//			break;
	//		}
	//	}

	public CNF getClausesWithoutAbstract() {
		return getSlicedCNF(0);
	}

	public CNF getClausesWithoutHidden() {
		return getSlicedCNF(1);
	}

	public CNF getClausesWithoutAbstractAndHidden() {
		return getSlicedCNF(2);
	}

	public CNF getFeatureTreeClauses() {
		final Lock slicingLock = slicingLocks[3];
		slicingLock.lock();
		try {
			CNF slicedCNF = slicedCNFs[3];
			if (slicedCNF == null) {
				final AdvancedNodeCreator nodeCreator = new AdvancedNodeCreator(featureModel);
				nodeCreator.setModelType(ModelType.OnlyStructure);
				nodeCreator.setCnfType(CNFType.Regular);
				nodeCreator.setIncludeBooleanValues(false);
				slicedCNF = new FeatureModelCNF(featureModel, false);
				slicedCNF.addClauses(Nodes.convert(slicedCNF.getVariables(), nodeCreator.createNodes()));
				slicedCNFs[3] = slicedCNF;
			}
			return slicedCNF;
		} finally {
			slicingLock.unlock();
		}
	}

	public CNF getEmptyCNF() {
		final Lock slicingLock = slicingLocks[4];
		slicingLock.lock();
		try {
			CNF slicedCNF = slicedCNFs[4];
			if (slicedCNF == null) {
				slicedCNF = new FeatureModelCNF(featureModel, false);
				slicedCNFs[4] = slicedCNF;
			}
			return slicedCNF;
		} finally {
			slicingLock.unlock();
		}
	}

}
