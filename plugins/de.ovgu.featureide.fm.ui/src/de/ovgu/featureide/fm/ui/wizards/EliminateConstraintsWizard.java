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
package de.ovgu.featureide.fm.ui.wizards;

import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.ui.INewWizard;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.conversion.CNFConverter;
import de.ovgu.featureide.fm.core.conversion.ComplexConstraintConverter;
import de.ovgu.featureide.fm.core.conversion.IConverterStrategy;
import de.ovgu.featureide.fm.core.conversion.NNFConverter;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * TODO description
 * 
 * @author Alexander
 */
public class EliminateConstraintsWizard extends AbstractWizard implements INewWizard {	
	protected static enum ConversionMethod {
		NNF, CNF, /*TSEITIN,*/ BEST;
	}

	private EliminateConstraintsPage page;
	private ConversionMethod method;
	private IFile inputModelFile;
	/**
	 * @param title
	 */
	public EliminateConstraintsWizard(IFile file, String title) {
		super(title);
		// TODO Auto-generated constructor stub
		inputModelFile = file;
	}
	
	@Override
	public void addPages() {
		setWindowTitle("Export Product-Equivalent Model Without Complex Constraints");
		page = new EliminateConstraintsPage(inputModelFile, "Export feature model to a product-equivalent model "
				+ "including only simple requires and excludes constraints.");
		addPage(page);
	}
	
	public IConverterStrategy getStrategy() {
		switch(page.selectedMethod) {
		case CNF:
			return new CNFConverter();
		case NNF:
		default:
			return new NNFConverter();
		}
	}
	
	public boolean preserveConfigurations() {
		return page.preserveConfigurations;
	}
}
