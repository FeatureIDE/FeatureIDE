package de.ovgu.featureide.fm.ui.views.constraintview.content;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.views.constraintview.util.ConstraintColorPair;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;

import java.util.ArrayList;
import java.util.List;

public class ConstraintViewContentProvider implements ITreeContentProvider {

    @Override
    public Object[] getElements(Object inputElement) {
        // TODO comment
        if(inputElement instanceof String){
            return new String[]{(String) inputElement};
        } else {
            IFeatureModel featureModel = (IFeatureModel) inputElement;
            return featureModel.getConstraints().toArray();
        }
    }

    @Override
    public Object[] getChildren(Object parentElement) {
        return new Object[0];
    }

    @Override
    public Object getParent(Object element) {
        return null;
    }

    @Override
    public boolean hasChildren(Object element) {
        return false;
    }


}
