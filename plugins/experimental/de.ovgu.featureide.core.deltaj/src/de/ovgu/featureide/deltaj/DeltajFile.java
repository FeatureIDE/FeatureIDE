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
package de.ovgu.featureide.deltaj;

import org.eclipse.core.resources.IFile;

/**
 * @author Sven Schuster
 */
public class DeltajFile {
	private IFile member;
	private int startLine;
	private int endLine;
	
	/**
	 * @param member
	 * @param startLine
	 * @param endLine
	 */
	public DeltajFile(IFile member, int startLine, int endLine) {
		this.member = member;
		this.startLine = startLine;
		this.endLine = endLine;
	}

	/**
	 * @return the member
	 */
	public IFile getMember() {
		return member;
	}

	/**
	 * @param member the member to set
	 */
	public void setMember(IFile member) {
		this.member = member;
	}

	/**
	 * @return the startLine
	 */
	public int getStartLine() {
		return startLine;
	}

	/**
	 * @param startLine the startLine to set
	 */
	public void setStartLine(int startLine) {
		this.startLine = startLine;
	}

	/**
	 * @return the endLine
	 */
	public int getEndLine() {
		return endLine;
	}

	/**
	 * @param endLine the endLine to set
	 */
	public void setEndLine(int endLine) {
		this.endLine = endLine;
	}
}
