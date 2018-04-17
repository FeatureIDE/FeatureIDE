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
package de.ovgu.featureide.fm.attributes.base.exceptions;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttributeParsedData;

/**
 * TODO description
 *
 * @author Joshua
 */
public class FeatureAttributeParseException extends Exception {

	private static final long serialVersionUID = 6366719326744299124L;

	IFeatureAttributeParsedData data;

	public FeatureAttributeParseException(IFeatureAttributeParsedData data) {
		this.data = data;
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Throwable#getMessage()
	 */
	@Override
	public String getMessage() {
		final StringBuilder builder = new StringBuilder();
		builder.append("The value of the feature attribute \"");
		builder.append(data.getName());
		builder.append("\" cannot be parsed to the type \"");
		builder.append(data.getType());
		builder.append("\"");
		return builder.toString();
	}

}
