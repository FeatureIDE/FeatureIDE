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
package de.ovgu.featureide.cloneanalysis.impl;

import java.util.Iterator;

import net.sourceforge.pmd.cpd.CPD;
import net.sourceforge.pmd.cpd.Match;
import de.ovgu.featureide.cloneanalysis.pmd.CPDAdapter;
import de.ovgu.featureide.cloneanalysis.pmd.ICloneAnalyzerAdapter;

public class CPDCloneAnalysis {
	private ICloneAnalyzerAdapter<CPD> cpdAdapter;

	public CPDCloneAnalysis() {
		cpdAdapter = new CPDAdapter();
	}

	public CPDCloneAnalysis(String filteredName) {
		cpdAdapter = new CPDAdapter(filteredName);
	}

	public Iterator<Match> analyze(Object selection) {
		// System.out.println("Starting CC analysis..");

		cpdAdapter.initializeTool();
		cpdAdapter.registerFilesForAnalysis(selection);
		cpdAdapter.startAnalysis();

		// System.out.println("CC analysis done!");

		return cpdAdapter.getMatches();
	}

	/**
	 * @return the cpdAdapter
	 */
	public ICloneAnalyzerAdapter<CPD> getCpdAdapter() {
		return cpdAdapter;
	}

}
