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
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.conversion.ComplexConstraintConverter;
import de.ovgu.featureide.fm.core.conversion.ComplexConstraintConverter.Option;
import de.ovgu.featureide.fm.core.conversion.IConverterStrategy;
import de.ovgu.featureide.fm.core.conversion.NNFConverter;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.ui.handlers.base.AFileHandler;
import de.ovgu.featureide.fm.ui.wizards.EliminateConstraintsWizard;

/**
 * TODO description
 *
 * @author Alexander
 */
public class EliminateComplexConstraintsHandler extends AFileHandler {

	@Override
	protected void singleAction(IFile file) {
		final IFeatureModel featureModel = FeatureModelManager.load(Paths.get(file.getLocationURI())).getObject();

		IConverterStrategy strategy = new NNFConverter();
		final ComplexConstraintConverter converter = new ComplexConstraintConverter();
		String path = "";

		final boolean trivial = ComplexConstraintConverter.trivialRefactoring(featureModel);

		int pseudo = 0, strict = 0;
		for (final IConstraint c : featureModel.getConstraints()) {
			if (ComplexConstraintConverter.isSimple(c.getNode())) {} else if (ComplexConstraintConverter.isPseudoComplex(c.getNode())) {
				pseudo++;
			} else {
				strict++;
			}
		}

		// count number of constraints
		// set file extension
		final EliminateConstraintsWizard wizard = new EliminateConstraintsWizard(file, "Complex-constraints elimination", trivial, pseudo, strict, "xml");

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

		final IFeatureModel result = converter.convert(featureModel, strategy, options.toArray(new Option[options.size()]));

		SimpleFileHandler.save(Paths.get(path), result, FMFormatManager.getInstance().getFormatByFileName(path));
	}

	@SuppressWarnings("unused")
	private void openFileInEditor(IFile outputFile) throws PartInitException {
		final IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		final IEditorInput editorInput = new FileEditorInput(outputFile);
		final IEditorReference[] refs = page.getEditorReferences();
		for (int i = 0; i < refs.length; i++) {
			if (refs[i].getEditorInput().equals(editorInput)) {
				page.closeEditor(refs[i].getEditor(false), false);
				break;
			}

		}
		IDE.openEditor(page, outputFile);
	}

}
