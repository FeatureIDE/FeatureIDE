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
package de.ovgu.featureide.munge.ui.outline;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineProvider;

/**
 * 
 * Implements all functions needed for the FeatureIDE outline
 * 
 * @author Christopher Sontag
 */
public class MungeOutline extends OutlineProvider {

	private static final Set<String> supportedTypes = new HashSet<>();
	static {
		supportedTypes.add("java");
		supportedTypes.add("jak");
		supportedTypes.add("hs");
		supportedTypes.add("h");
		supportedTypes.add("c");
		supportedTypes.add("cs");
		supportedTypes.add("asm");
	}
	
	public MungeOutline() {
		super(new MungeExtendedContentProvider(), new MungeOutlineLabelProvider());
	}

	@Override
	public boolean checkSupported(String extension) {
		return supportedTypes.contains(extension);
	}

	@Override
	public void handleUpdate(Viewer viewer, IFile iFile) {
		viewer.setInput(iFile);
	}

}
