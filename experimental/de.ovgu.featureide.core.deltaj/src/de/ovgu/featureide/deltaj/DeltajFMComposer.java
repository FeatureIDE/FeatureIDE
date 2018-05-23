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
package de.ovgu.featureide.deltaj;

import de.ovgu.featureide.fm.core.FMComposerExtension;

/**
 * DeltaJ specific feature model extensions.
 * 
 * @author Jens Meinicke
 */
public class DeltajFMComposer extends FMComposerExtension {

	private static String ORDER_PAGE_MESSAGE = 
			"FeatureIDE projects based on DeltaJ do not need a total order\n" +
			"as a partial order can be given directly in the delta modules\n" +
			"using the keyword 'after'.";

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.fm.core.IFMComposerExtension#getComposerName()
	 */
	@Override
	public String getOrderPageMessage() {
		return ORDER_PAGE_MESSAGE;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.fm.core.IFMComposerExtension#hasFeaureOrder()
	 */
	@Override
	public boolean hasFeaureOrder() {
		return false;
	}

}
