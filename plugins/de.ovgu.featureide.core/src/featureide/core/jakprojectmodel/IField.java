/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package featureide.core.jakprojectmodel;

import org.eclipse.core.resources.IFile;

public interface IField extends IJakModelElement {

	public String getIdentifier();

	public void setOwn(IFile file);

	public boolean isOwn(IFile file);

	public void setAvailible(IFile file);

	public boolean isAvailible(IFile file);

	public void setLineNumber(IFile file, int lineNumber);

	public int getLineNumber(IFile file);

	public String getFieldName();
	
	public boolean isPublic();
	
	public boolean isPrivate();
	
	public boolean isProtected();
	
	public boolean isStatic();
	
	public boolean isFinal();

}
