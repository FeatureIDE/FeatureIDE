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
	private ErrorEnum error;
	private int startErrorIndex;
	private int endErrorIndex;
	private String keyword;

	public ErrorType(ErrorEnum error, int startErrorIndex, int endErrorIndex) {
		setError(error);
		setStartErrorIndex(startErrorIndex);
		setEndErrorIndex(endErrorIndex);
	}

	public ErrorType(ErrorEnum error) {
		setError(error);
	}

	public ErrorType(ErrorEnum error, String keyword) {
		setError(error);
		setKeyword(keyword);
	}

	/**
	 * @return the error
	 */
	public ErrorEnum getError() {
		return error;
	}

	/**
	 * @param error the error to set
	 */
	public void setError(ErrorEnum error) {
		this.error = error;
	}

	/**
	 * @return the startErrorIndex
	 */
	public int getStartErrorIndex() {
		return startErrorIndex;
	}

	/**
	 * @param startErrorIndex the startErrorIndex to set
	 */
	public void setStartErrorIndex(int startErrorIndex) {
		this.startErrorIndex = startErrorIndex;
	}

	/**
	 * @return the endErrorIndex
	 */
	public int getEndErrorIndex() {
		return endErrorIndex;
	}

	/**
	 * @param endErrorIndex the endErrorIndex to set
	 */
	public void setEndErrorIndex(int endErrorIndex) {
		this.endErrorIndex = endErrorIndex;
	}

	/**
	 * @return the keyword
	 */
	public String getKeyword() {
		return keyword;
	}

	/**
	 * @param keyword the keyword to set
	 */
	public void setKeyword(String keyword) {
		this.keyword = keyword;
	}

	public enum ErrorEnum {
		None, InvalidFeatureName, InvalidExpressionLeft, InvalidExpressionRight, Default
	}
}
