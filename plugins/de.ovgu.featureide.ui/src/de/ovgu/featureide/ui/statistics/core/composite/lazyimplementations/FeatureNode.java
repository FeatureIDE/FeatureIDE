package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.ui.statistics.core.composite.IToolTip;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Evaluates a feature by showing its attributes and description in a tool tip
 * and by displaying child features and constraints as further child nodes in
 * the {@link TreeViewer}
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class FeatureNode extends LazyParent implements IToolTip {
	private static final String TOOLTIP_SEPARATOR = " | ";
	protected String tooltip;
	private boolean hasConstraints;
	private Feature feat;

	public FeatureNode(final Feature feat) {
		super(feat.toString());
		this.feat = feat;
		this.tooltip = buildToolTip();
		hasConstraints = !feat.getRelevantConstraints().isEmpty();
		if (!(feat.hasChildren() || hasConstraints)) {
			lazy = false;
		}
	}
	
	/**
	 * Creates child nodes for constraints affecting this feature and child
	 * features of this feature. If both are present each category is stored in
	 * a separate node.
	 */
	@Override
	protected void initChildren() {
		
		if (feat.hasChildren() && hasConstraints) {
			addChild(findChildFeatures(new Parent("Child features: ", null)));
			addChild(findConstraints(new Parent("Constraints: ", null)));
		} else {
			findChildFeatures(this);
			findConstraints(this);
		}
	}
	
	/*
	 * Is called when a tooltip is requested. The tooltip is built in this
	 * manner:
	 * 
	 * <attribute_1> | <attribute_2> | ... | <attribute_n> [Description:
	 * <description>]
	 */
	private String buildToolTip() {
		List<String> attribute = new ArrayList<String>();
		FeatureStatus status = feat.getFeatureStatus();
		
		if (status != FeatureStatus.NORMAL && status != FeatureStatus.INDETERMINATE_HIDDEN) {
			attribute.add("STATUS: " + status);
		}
		
		if (feat.isAbstract()) {
			attribute.add("abstract");
		} else {
			attribute.add("concrete");
		}
		
		if (feat.isMandatory()) {
			attribute.add("mandatory");
		} else {
			attribute.add("optional");
		}
		
		String connectionType = null;
		if (feat.isAlternative()) {
			connectionType = "alternative";
		} else if (feat.isOr()) {
			connectionType = "or";
		} else if (feat.isAnd()) {
			connectionType = "and";
		}
		attribute.add(connectionType + " - connection");
		
		if (status == FeatureStatus.INDETERMINATE_HIDDEN) {
			attribute.add("hidden by ancestor");
		} else if (feat.isHidden()) {
			attribute.add("hidden");
		}
		
		if (feat.hasChildren()) {
			attribute.add("has child-features");
		} else {
			attribute.add("is terminal");
		}
		
		if (hasConstraints) {
			attribute.add("is affected by constraints");
		}
		
		StringBuilder buffer = new StringBuilder();
		buffer.append("attributes: ");
		for (int i = 0; i < attribute.size() - 1; i++) {
			buffer.append(attribute.get(i));
			buffer.append(TOOLTIP_SEPARATOR);
		}
		buffer.append(attribute.get(attribute.size() - 1));
		
		printDescription(buffer);
		return buffer.toString();
	}
	
	/**
	 * Adds the description to the features tooltip, if it has one.
	 */
	private void printDescription(StringBuilder buffer) {
		String featDesc = feat.getDescription();
		if (featDesc != null && !featDesc.equals("")) {
			buffer.append("\n");
			buffer.append("Description: ");
			buffer.append(featDesc);
		}
	}
	
	private Parent findConstraints(Parent constraints) {
		if (hasConstraints) {
			for (Constraint constr : feat.getRelevantConstraints()) {
				constraints.addChild(new Parent("Constraint", constr.toString()));
			}
		}
		return constraints;
	}
	
	private Parent findChildFeatures(Parent childFeat) {
		if (feat.hasChildren()) {
			for (Feature temp : feat.getChildren()) {
				childFeat.addChild(new FeatureNode(temp));
			}
		}
		return childFeat;
	}
	
	@Override
	public String getToolTip() {
		return buildToolTip();
	}
}