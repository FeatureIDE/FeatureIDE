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
package de.ovgu.featureide.fm.core.io;

import java.util.Arrays;
import java.util.Collection;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Reads / Writes a feature order file.
 *
 * @author Sebastian Krieter
 */
public class FeatureOrderFormat extends APersistentFormat<IFeatureModel> implements IPersistentFormat<IFeatureModel> {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + FeatureOrderFormat.class.getSimpleName();

	@Override
	public ProblemList read(IFeatureModel object, CharSequence source) {
		final String[] lines = source.toString().split("[\n|\r]+");
		object.setFeatureOrderList(Arrays.asList(lines));
		return new ProblemList();
	}

	@Override
	public String write(IFeatureModel object) {
		final String newLine = System.getProperty("line.separator");
		final StringBuilder sb = new StringBuilder();

		sb.append(((object.isFeatureOrderUserDefined()) ? "true" : "false") + newLine);

		Collection<String> list = object.getFeatureOrderList();
		if (list.isEmpty()) {
			list = FeatureUtils.extractConcreteFeaturesAsStringList(object);
		}

		for (final String featureName : list) {
			sb.append(featureName);
			sb.append(newLine);
		}

		return sb.toString();
	}

	@Override
	public String getSuffix() {
		return "order";
	}

	@Override
	public FeatureOrderFormat getInstance() {
		return this;
	}

	@Override
	public boolean supportsRead() {
		return true;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public String getName() {
		return "FeatureIDE";
	}

}
