package de.ovgu.featureide.fm.ui.views.constraintview.content;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.views.constraintview.util.ConstraintColorPair;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.sat4j.specs.IConstr;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

public class ConstraintViewFilter extends ViewerFilter {

    private List<FeatureEditPart> selection;
    private List<IConstraint> explanationConstraints = new ArrayList<>();;
    private String searchText = "";
    private boolean caseSensitive = false;

    public void setActiveExplanation(Explanation<?> activeExplanation) {
        explanationConstraints.clear();

        if(activeExplanation == null){
            return;
        }

        for (final Reason<?> r : activeExplanation.getReasons()) {
            if (r.getSubject() instanceof FeatureModelToNodeTraceModel.FeatureModelElementTrace) {
                IFeatureModelElement element =  ((FeatureModelToNodeTraceModel.FeatureModelElementTrace) r.getSubject()).getElement();
                if (element instanceof IConstraint) {
                    explanationConstraints.add((IConstraint) element);
                }
            }
        }
    }

    public void setFeatureModelSelection(List<FeatureEditPart> selection){
        this.selection = selection;
    }

    public List<FeatureEditPart> getFeatureModelSelection() {
        return selection;
    }

    public void setSearchText(String searchText){
        this.searchText = searchText;
    }

    @Override
    public boolean select(Viewer viewer, Object parentElement, Object element) {
        // TODO comment
        if(element instanceof String){
            return true;
        }
        IConstraint constraint = (IConstraint) element;

        // filter by selection and explanation
        if(selection != null && ! selection.isEmpty()){

            if( !constraintInSelection(constraint) && !constraintInExplanation(constraint)){
                return false;
            }
        }


        // filter by search text
        if(searchText != null && !searchText.isEmpty()){
            if( !constraintInSearch(constraint)){
                return false;
            }
        }

        return true;
    }

    private boolean constraintInExplanation(IConstraint constraint){
        return explanationConstraints.contains(constraint);
    }

    private boolean constraintInSearch(IConstraint constraint){
        String currentSearchText = this.searchText;
        String constraintText = constraint.getDisplayName();
        String constraintDescription = constraint.getDescription();

        constraintDescription = constraintDescription.replaceAll("\n", " ");
        constraintDescription = constraintDescription.replaceAll("\r", " ");

        if(! caseSensitive) {
            constraintText = constraintText.toLowerCase();
            constraintDescription = constraintDescription.toLowerCase();
            currentSearchText = currentSearchText.toLowerCase();
        }

        String regexSearch = ".*" +  currentSearchText + ".*";

        // to avoid problems when invalid regex searches are entered
        try {
            return (constraintText.matches(regexSearch)
                    || constraintDescription.matches(regexSearch));
        }catch (PatternSyntaxException e) {
            return (constraintText.contains(currentSearchText)
                    || constraintDescription.contains(currentSearchText));
        }
    }

    private boolean constraintInSelection(IConstraint constraint){
        for (FeatureEditPart featureEditPart : selection){
            if(matchesConstraint(featureEditPart, constraint)){
                return true;
            }
        }
        return false;
    }


    private boolean matchesConstraint(FeatureEditPart part, IConstraint constraint) {
        final IGraphicalFeature model = part.getModel();
        if ( model == null ){
            return false;
        }
        final String partName = model.toString();
        final String constraintName = constraint.getDisplayName();
        return constraintName.matches(".*( |^)-*" + partName + "( |$).*");
    }

    public List<FeatureEditPart> getSelection() {
        return selection;
    }
}
