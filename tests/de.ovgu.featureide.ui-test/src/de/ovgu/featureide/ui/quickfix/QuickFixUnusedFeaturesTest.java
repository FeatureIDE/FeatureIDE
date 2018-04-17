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
package de.ovgu.featureide.ui.quickfix;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.base.impl.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 * Creates configurations where false optional features are unused.
 *
 * @author Jens Meinicke
 */
@RunWith(Parameterized.class)
public class QuickFixUnusedFeaturesTest {

	QuickFixUnusedFeatures quickFix = new QuickFixUnusedFeatures(null);

	protected String failureMessage;

	private final FeatureModel fm;

	public QuickFixUnusedFeaturesTest(FeatureModel fm, String s) throws UnsupportedModelException {
		this.fm = fm;
		failureMessage = "(" + s + ")";

	}

	@Parameters
	public static Collection<Object[]> getModels() throws FileNotFoundException, UnsupportedModelException {
		final Collection<Object[]> params = new ArrayList<>();
		for (final File f : Commons.getFeatureModelFolder().listFiles(getFileFilter(".xml"))) {
			final Object[] models = new Object[2];

			final IFeatureModel fm = DefaultFeatureModelFactory.getInstance().createFeatureModel();
			SimpleFileHandler.load(f.toPath(), fm, FMFormatManager.getInstance());
			models[0] = fm;
			models[1] = f.getName();
			params.add(models);
		}

		return params;
	}

	private final static FileFilter getFileFilter(final String s) {
		final FileFilter filter = new FileFilter() {

			@Override
			public boolean accept(File pathname) {
				return pathname.getName().endsWith(s);
			}
		};
		return filter;
	}

	@Test
	public void createConfigurationsTest() {
		final Collection<IFeature> concrete = FeatureUtils.getConcreteFeatures(fm);
		final Collection<IFeature> core = fm.getAnalyser().getCoreFeatures();
		final Collection<IFeature> dead = fm.getAnalyser().getDeadFeatures();
		final Collection<String> falseOptionalFeatures = new LinkedList<String>();

		for (final IFeature feature : concrete) {
			if (!core.contains(feature) && !dead.contains(feature)) {
				falseOptionalFeatures.add(feature.getName());
			}
		}

		final Collection<String> falseOptionalFeaturesTest = new ArrayList<String>(falseOptionalFeatures);
		final Collection<Configuration> confs = quickFix.createConfigurations(falseOptionalFeatures, fm);
		for (final Configuration conf : confs) {
			for (final SelectableFeature feature : conf.getFeatures()) {
				if (feature.getSelection() == Selection.SELECTED) {
					falseOptionalFeaturesTest.remove(feature.getName());
				}
			}
		}
		assertTrue(failureMessage, falseOptionalFeaturesTest.isEmpty());
	}
}
