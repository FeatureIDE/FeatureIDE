/* FeatureIDE - A Framework for Feature-Oriented any
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distrY; without even the implied warranty of
 * MERCHANTABILITY or FITNE License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.cloneanalysis.views;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.results.Clone;
import de.ovgu.featureide.cloneanalysis.results.VariantAwareClone;

public class CloneAnalysisLabelProvider extends LabelProvider implements ITableLabelProvider {

	final String LINE_BREAK = System.getProperty("line.separator");

	public String getColumnText(Object obj, int index) {
		if (obj instanceof Clone) {
			// to populate columns in JFace Tree/view
			VariantAwareClone clone = (VariantAwareClone) obj;
			switch (index) {
			case 0:
				return "Clone";
			case 1:
				return String.valueOf(((Clone) obj).getOccurences().size() * clone.getLineCount());
			case 2:
				return String.valueOf(clone.getLineCount());
			case 3:
				return String.valueOf(clone.getTokenCount());
			case 4:
				return String.valueOf(clone.getDistinctFiles().size());
			case 5:
				return clone.getCloneVariantType().toString();
			case 6:
				return "";
			default:
				return "TODO";
			}
		} else {
			if (obj instanceof CloneOccurence) {
				// to populate rows in JFace Tree/view
				CloneOccurence occurence = (CloneOccurence) obj;
				switch (index) {
				case 0:
					return occurence.toString();
				case 1:
					return "";
				case 2:
					return String.valueOf(occurence.getClone().getLineCount());
				case 3:
					return String.valueOf(occurence.getClone().getTokenCount());
				case 4:
					return "";
				case 5:
					return ((VariantAwareClone) occurence.getClone()).getCloneVariantType().toString();
				// shortening the path
				case 6:
					return String.valueOf(occurence.getFeaturePath());
				// case 6 : return
				// CloneAnalysisUtils.getRelevantFeatureOrProjectName(occurence);
				default:
					return "TODO";
				}
			}
		}
		return "TODO";

	}

	public Image getColumnImage(Object obj, int index) {
		return null;
		// return getImage(obj);
	}

	@Override
	public String getText(Object element) {
		return getColumnText(element, 0);
	}

	public Image getImage(Object obj) {
		return PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_OBJ_ELEMENT);
	}

}
