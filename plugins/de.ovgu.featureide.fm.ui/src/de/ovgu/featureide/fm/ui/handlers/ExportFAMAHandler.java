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
package de.ovgu.featureide.fm.ui.handlers;

import java.io.File;
import java.io.FileNotFoundException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.conversion.ComplexConstraintConverter;
import de.ovgu.featureide.fm.core.conversion.ComplexConstraintConverter.Option;
import de.ovgu.featureide.fm.core.conversion.IConverterStrategy;
import de.ovgu.featureide.fm.core.conversion.NNFConverter;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.fama.FAMAFormat;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.handlers.base.AFileHandler;
import de.ovgu.featureide.fm.ui.wizards.EliminateConstraintsWizard;

/**
 * Exports feature model to FAMA format.
 *
 * @author Alexander Knueppel
 */
public class ExportFAMAHandler extends AFileHandler {

	@Override
	protected void singleAction(IFile file) {
		final IFeatureModel fm = readModel(file);

		IConverterStrategy strategy = new NNFConverter();
		final ComplexConstraintConverter converter = new ComplexConstraintConverter();
		String path = "";
		final boolean trivial = ComplexConstraintConverter.trivialRefactoring(fm);

		if (!trivial && !MessageDialog.openQuestion(new Shell(), "Warning!",
				"Complex constraints of current feature model cannot be transformed trivially! Proceed? (Feature model will become bigger.)")) {
			return;
		}

		int pseudo = 0, strict = 0;
		for (final IConstraint c : fm.getConstraints()) {
			if (ComplexConstraintConverter.isSimple(c.getNode())) {} else if (ComplexConstraintConverter.isPseudoComplex(c.getNode())) {
				pseudo++;
			} else {
				strict++;
			}
		}

		final EliminateConstraintsWizard wizard = new EliminateConstraintsWizard(file, "Complex-constraints elimination", trivial, pseudo, strict, "fm");

		final List<Option> options = new ArrayList<Option>();
		if (Window.OK == new WizardDialog(Display.getCurrent().getActiveShell(), wizard).open()) {
			strategy = wizard.getStrategy();
			if (wizard.preserveConfigurations()) {
				options.add(Option.COHERENT);
			}
			if (wizard.removeRedundancy()) {
				options.add(Option.REMOVE_RDUNDANCY);
			}
			path = wizard.getPath();
			if ((new File(path)).exists() && !MessageDialog.openQuestion(new Shell(), "Warning!", "Selected file already exists. File will be overwritten.")) {
				return;
			}

		}

		final IFeatureModel result = converter.convert(fm, strategy, options.toArray(new Option[options.size()]));
		SimpleFileHandler.save(Paths.get(path), result, new FAMAFormat());
	}

	/**
	 * reads the featureModel from file
	 *
	 * @param inputFile
	 * @return featureModel
	 * @throws UnsupportedModelException
	 * @throws FileNotFoundException
	 */
	private IFeatureModel readModel(IFile inputFile) {
		final IFeatureModelFormat format = FMFormatManager.getInstance().getFormatByFileName(inputFile.getName());
		IFeatureModel fm;
		try {
			fm = FMFactoryManager.getFactory(inputFile.getLocation().toString(), format).createFeatureModel();
		} catch (final NoSuchExtensionException e) {
			fm = FMFactoryManager.getDefaultFactory().createFeatureModel();
		}
		try {
			SimpleFileHandler.load(inputFile.getContents(), fm, format);
		} catch (final CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return fm;
	}
}
