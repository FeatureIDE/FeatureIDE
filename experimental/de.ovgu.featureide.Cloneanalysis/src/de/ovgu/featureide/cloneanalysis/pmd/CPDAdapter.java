package de.ovgu.featureide.cloneanalysis.pmd;

import java.io.File;
import java.io.IOException;
import java.util.Iterator;

import net.sourceforge.pmd.cpd.CPD;
import net.sourceforge.pmd.cpd.CPDConfiguration;
import net.sourceforge.pmd.cpd.CPDListener;
import net.sourceforge.pmd.cpd.Match;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.IStructuredSelection;

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
		if (files instanceof IStructuredSelection)
			addResourcesFromSelection((IStructuredSelection) files);
		else if (files instanceof IProject)
			addProjectToAnalysis((IProject) files);
		else
			assert false : ("adding files of type " + files.getClass() + "is not supported(yet)");
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
