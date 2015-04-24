/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
	
	protected final String tooltip;
	
	private final boolean hasConstraints, expand;
	private final Feature feat;

	public FeatureNode(final Feature feat, boolean expand) {
		super(feat.toString());
		this.feat = feat;
		this.expand = expand;
		this.tooltip = buildToolTip();
		hasConstraints = !feat.getRelevantConstraints().isEmpty();
		if (!(feat.hasChildren() || hasConstraints)) {
			lazy = false;
		}
	}
	
	@Override
	public Boolean hasChildren() {
		return expand && super.hasChildren();
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
				childFeat.addChild(new FeatureNode(temp, expand));
			}
		}
		return childFeat;
	}
	
	@Override
	public String getToolTip() {
		return buildToolTip();
	}
}
