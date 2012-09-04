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
			if(((ContentProposal)element).getContent().equals("not")){
				return OPERATOR_SYMBOL;
			}
			if(((ContentProposal)element).getContent().equals("or")){
				return OPERATOR_SYMBOL;
			}
			if(((ContentProposal)element).getContent().equals("and")){
				return OPERATOR_SYMBOL;
			}
			if(((ContentProposal)element).getContent().equals("iff")){
				return OPERATOR_SYMBOL;
			}
			if(((ContentProposal)element).getContent().equals("implies")){
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
