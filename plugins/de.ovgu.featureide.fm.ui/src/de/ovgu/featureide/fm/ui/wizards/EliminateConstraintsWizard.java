/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

import org.eclipse.core.resources.IFile;
import org.eclipse.ui.INewWizard;

import de.ovgu.featureide.fm.core.conversion.CNFConverter;
import de.ovgu.featureide.fm.core.conversion.CombinedConverter;
import de.ovgu.featureide.fm.core.conversion.IConverterStrategy;
import de.ovgu.featureide.fm.core.conversion.NNFConverter;

/**
 * TODO description
 *
 * @author Alexander
 */
public class EliminateConstraintsWizard extends AbstractWizard implements INewWizard {

	protected static enum ConversionMethod {
		NNF, CNF, /* TSEITIN, */ COMBINED;
	}

	private EliminateConstraintsPage page;
	private ConversionMethod method;
	private final IFile inputModelFile;
	private String path;
	private final boolean trivial;
	private final int pseudocomplex;
	private final int strictcomplex;
	private final String fileExtension;

	/**
	 * @param title
	 */
	public EliminateConstraintsWizard(IFile file, String title, boolean trivial, int pseudocomplex, int strictcomplex, String fileExtension) {
		super(title);
		// TODO Auto-generated constructor stub
		inputModelFile = file;
		this.trivial = trivial;
		this.pseudocomplex = pseudocomplex;
		this.strictcomplex = strictcomplex;
		this.fileExtension = fileExtension;
	}

	@Override
	public void addPages() {
		setWindowTitle("Export Product-Equivalent Model Without Complex Constraints");
		page = new EliminateConstraintsPage(inputModelFile, "Complex constraints elimination", trivial, fileExtension);

		if (strictcomplex == 0) {
			page.setTitle("No Strict-Complex Constraints found");
			page.setDescription("Number of pseudo-complex constraints: " + pseudocomplex);
		} else {
			page.setTitle("Strict-Complex Constraints found");
			page.setDescription("Number of strict-complex constraints: " + strictcomplex + "\n" + "Number of pseudo-complex constraints: " + pseudocomplex);
		}

		addPage(page);
	}

	public IConverterStrategy getStrategy() {
		switch (page.selectedMethod) {
		case CNF:
			return new CNFConverter();
		case NNF:
			return new NNFConverter();
		default:
			return new CombinedConverter();
		}
	}

	public String getPath() {
		return page.path;
	}

	public boolean preserveConfigurations() {
		return page.preserveConfigurations;
	}

	public boolean removeRedundancy() {
		return page.removeRedundancy;
	}
}
