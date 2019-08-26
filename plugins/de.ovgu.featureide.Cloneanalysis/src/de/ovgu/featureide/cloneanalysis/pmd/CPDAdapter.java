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

import java.io.IOException;
import java.util.Iterator;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.IStructuredSelection;

import net.sourceforge.pmd.cpd.CPD;
import net.sourceforge.pmd.cpd.CPDConfiguration;
import net.sourceforge.pmd.cpd.Match;

/**
 * @author Konstantin Tonscheidt
 * 
 */
public class CPDAdapter extends DefaultCloneAnalyzerAdapter<CPD> {

	private CPDConfiguration cloneAnalysisConfiguration = null;

	public CPDAdapter() {
		super(new DefaultFilenameFilter());
	}

	public CPDAdapter(String filteredName) {
		super(new FilteredFilenameFilter(filteredName));
	}

	public void setCPDConfiguration(CPDConfiguration configuration) {
		this.cloneAnalysisConfiguration = configuration;
	}

	@Override
	public void initializeTool() {
		cloneAnalysisConfiguration = createDefaultConfiguration();
		analysisTool = new CPD(cloneAnalysisConfiguration);
		// analysisTool.setCpdListener(new CPDListener()
		// {
		//
		// @Override
		// public void phaseUpdate(int phase)
		// {
		// System.out.println("Phase " + phase + " entered!");
		// }
		//
		// @Override
		// public void addedFile(int fileCount, File file)
		// {
		// if(file!=null)
		// System.out.println("Added File: " + file.getName());
		// }
		// });
	}

	@Override
	public void registerFilesForAnalysis(Object files) {
		assert files != null : "files must not be null...";
		if (files instanceof IStructuredSelection) addResourcesFromSelection((IStructuredSelection) files);
		else if (files instanceof IProject) addProjectToAnalysis((IProject) files);
		else assert false : ("adding files of type " + files.getClass() + "is not supported(yet)");
	}

	@Override
	public Object startAnalysis() {
		analysisTool.go();
		return null;
	}

	@Override
	protected void registerContainerRecursively(IContainer container) {
		try {
			analysisTool.addRecursively(container.getLocation().toString());
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	@Override
	public Iterator<Match> getMatches() {
		return analysisTool.getMatches();
	}
}
