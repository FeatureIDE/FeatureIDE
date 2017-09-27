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

import org.eclipse.ui.INewWizard;

import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 *
 * @author Sebastian Krieter
 */
public class FeatureModelConversionWizard extends AbstractWizard implements INewWizard {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".wizzard.FeatureModelConversionWizzard";

	public FeatureModelConversionWizard() {
		super("Convert Feature Models");
	}

	@Override
	public void addPages() {
		addPage(new FeatureModelConversionPage());
	}

	public String getOutputFolder() {
		return (String) getData(WizardConstants.KEY_OUT_FOLDER);
	}

	public IFeatureModelFormat getInputFormat() {
		final Object data = getData(WizardConstants.KEY_OUT_INPUTFORMAT);
		if (data != null) {
			try {
				return FMFormatManager.getInstance().getExtension((String) data);
			} catch (final NoSuchExtensionException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
		return null;
	}

	public IFeatureModelFormat getOutputFormat() {
		final Object data = getData(WizardConstants.KEY_OUT_OUTPUTFORMAT);
		if (data != null) {
			try {
				return FMFormatManager.getInstance().getExtension((String) data);
			} catch (final NoSuchExtensionException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
		return null;
	}

}
