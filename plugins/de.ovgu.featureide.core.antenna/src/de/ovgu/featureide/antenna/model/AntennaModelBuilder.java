/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.antenna.model;


import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.preprocessor.PPModelBuilder;

/**
 * Build the FSTModel for antenna projects.
 * 
 * @author Christoph Giesel
 * @author Marcus Kamieth
 */
public class AntennaModelBuilder extends PPModelBuilder {
	
	public static final String OPERATORS = "[\\s!=<>\",;&\\^\\|]";
	public static final String REGEX = "(//#.*" + OPERATORS + ")(%s)(" + OPERATORS + ")";
	
	public AntennaModelBuilder(IFeatureProject featureProject) {
		super(featureProject);
	}

	@Override
	protected boolean containsFeature(String text, String feature) {
		return contains(text, feature);
	}
	
	/**
	 * the Pattern:
	 * <ul><li>set flag DOTALL</li>
	 * <li>match any characters</li>
	 * <li>match any whitespace characters</li>
	 * <li>match "//# if/... [operators]feature[operators]"</li>
	 * <li>match any further characters</li></ul>
	 */
	public static boolean contains(String text, String feature){
		Pattern pattern = Pattern.compile(String.format(REGEX, feature));
		Matcher matcher = pattern.matcher(text);

		return matcher.find();
	}
}
