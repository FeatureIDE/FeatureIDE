/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
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
