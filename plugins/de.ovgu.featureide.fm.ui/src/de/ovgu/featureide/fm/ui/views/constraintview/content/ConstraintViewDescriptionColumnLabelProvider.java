package de.ovgu.featureide.fm.ui.views.constraintview.content;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.ui.views.constraintview.util.ConstraintColorPair;
import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.sat4j.specs.IConstr;

public class ConstraintViewDescriptionColumnLabelProvider extends ColumnLabelProvider {
    @Override
    public String getText(Object element) {
        // TODO comment
        if(element instanceof String){
            return "";
        }else {
            IConstraint constraint = (IConstraint) element;
            String descriptionText = constraint.getDescription();
            descriptionText = descriptionText.replaceAll("\n", " ");
            return descriptionText;
        }
    }
}
