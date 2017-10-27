package de.ovgu.featureide.cloneanalysis.views;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.results.Clone;
import de.ovgu.featureide.cloneanalysis.results.FeatureRootLocation;
import de.ovgu.featureide.cloneanalysis.results.VariantAwareClone;
import de.ovgu.featureide.cloneanalysis.utils.CloneAnalysisUtils;

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