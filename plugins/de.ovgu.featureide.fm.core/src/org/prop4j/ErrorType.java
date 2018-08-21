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
package org.prop4j;

/**
 * ErrorType class for NodeReader Errors
 * 
 * @author Mohammed Khaled
 */
public class ErrorType {
	public ErrorEnum error;
	public int startErrorIndex;
	public int endErrorIndex;
	public String keyword;

	public ErrorType(ErrorEnum error, int startErrorIndex, int endErrorIndex) {
		this.error = error;
		this.startErrorIndex = startErrorIndex;
		this.endErrorIndex = endErrorIndex;
	}

	public ErrorType(ErrorEnum error) {
		this.error = error;
	}

	public ErrorType(ErrorEnum error, String keyword) {
		this.error = error;
		this.keyword = keyword;
	}

	public enum ErrorEnum {
		None, InvalidFeatureName, InvalidExpressionLeft, InvalidExpressionRight, Default
	}
}
