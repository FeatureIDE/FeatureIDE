/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.AFormatHandler;
import de.ovgu.featureide.fm.core.io.ModelWarning;

/**
 * Reads / Writes a feature order file.
 * 
 * @author Sebastian Krieter
 */
public class FeatureOrderHandler extends AFormatHandler<IFeatureModel> {

	public FeatureOrderHandler(IFeatureModel object) {
		super(object);
	}

	@Override
	public List<ModelWarning> read(CharSequence source) {
		String[] lines = source.toString().split("[\n|\r]+");
		object.setFeatureOrderList(Arrays.asList(lines));
		return Collections.emptyList();
	}

	@Override
	public String write() {
		final String newLine = System.getProperty("line.separator");
		final StringBuilder sb = new StringBuilder();

		sb.append(((object.isFeatureOrderUserDefined()) ? "true" : "false") + newLine);

		Collection<String> list = object.getFeatureOrderList();
		if (list.isEmpty()) {
			list = FeatureUtils.extractConcreteFeaturesAsStringList(object);
		}

		for (String featureName : list) {
			sb.append(featureName);
			sb.append(newLine);
		}

		return sb.toString();
	}

	@Override
	public String getSuffix() {
		return "order";
	}

}
