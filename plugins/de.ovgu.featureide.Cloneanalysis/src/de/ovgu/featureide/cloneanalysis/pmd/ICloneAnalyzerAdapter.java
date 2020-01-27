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
package de.ovgu.featureide.cloneanalysis.pmd;

import java.util.Iterator;

import net.sourceforge.pmd.cpd.Match;

public interface ICloneAnalyzerAdapter<Tool> {

	/**
	 * Initializes the Tool which is used by the Adapter.
	 */
	public abstract void initializeTool();

	/**
	 * Register the files to be analyzed with the tool.
	 * 
	 * @param files the files
	 */
	public abstract void registerFilesForAnalysis(Object files);

	/**
	 * Starts the analysis and may return the analysis results.
	 * 
	 * @return the analysis results, or null.
	 */
	public abstract Object startAnalysis();

	public Iterator<Match> getMatches();

}
