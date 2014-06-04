/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * provides the pictures of constraints or operators in the content assist window
 *  
 * @author David Broneske
 * @author Fabian Benduhn
 */
public class ConstraintProposalLabelProvider extends LabelProvider implements GUIDefaults {

	/* (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ILabelProvider#getImage(java.lang.Object)
	 */
	@Override
	public Image getImage(Object element) {
		if(element instanceof ContentProposal){
			String content = ((ContentProposal)element).getContent();
			if("not".equals(content) || "or".equals(content) || "and".equals(content)
				|| "iff".equals(content) || "implies".equals(content)){
				return OPERATOR_SYMBOL;
			}	
		}
		return FEATURE_SYMBOL;
	}
	
	@Override
	public String getText(Object element){
	
		if(element instanceof ContentProposal){
			return ((ContentProposal)element).getContent();
		}
		return element.toString();
	}
	
}
