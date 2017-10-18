/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.ABSTRACT;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT;
import static de.ovgu.featureide.fm.core.localization.StringTable.HAS_CHILD_FEATURES;
import static de.ovgu.featureide.fm.core.localization.StringTable.HIDDEN;
import static de.ovgu.featureide.fm.core.localization.StringTable.HIDDEN_BY_ANCESTOR;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_AFFECTED_BY_CONSTRAINTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_TERMINAL;
import static de.ovgu.featureide.fm.core.localization.StringTable.MANDATORY;
import static de.ovgu.featureide.fm.core.localization.StringTable.OPTIONAL;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.ui.statistics.core.composite.IToolTip;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Evaluates a feature by showing its attributes and description in a tool tip and by displaying child features and constraints as further child nodes in the
 * {@link TreeViewer}
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class FeatureNode extends LazyParent implements IToolTip {

	private static final String TOOLTIP_SEPARATOR = " | ";

	protected final String tooltip;

	private final boolean hasConstraints, expand;
	private final IFeature feat;

	public FeatureNode(final IFeature feat, boolean expand) {
		super(feat.getName());
		this.feat = feat;
		this.expand = expand;
		tooltip = buildToolTip();
		hasConstraints = !feat.getStructure().getRelevantConstraints().isEmpty();
		if (!(feat.getStructure().hasChildren() || hasConstraints)) {
			lazy = false;
		}
	}

	@Override
	public Boolean hasChildren() {
		return expand && super.hasChildren();
	}

	/**
	 * Creates child nodes for constraints affecting this feature and child features of this feature. If both are present each category is stored in a separate
	 * node.
	 */
	@Override
	protected void initChildren() {
		if (feat.getStructure().hasChildren() && hasConstraints) {
			addChild(findChildFeatures(new Parent("Child features: ", null)));
			addChild(findConstraints(new Parent("Constraints: ", null)));
		} else {
			findChildFeatures(this);
			findConstraints(this);
		}
	}

	/*
	 * Is called when a tooltip is requested. The tooltip is built in this manner: <attribute_1> | <attribute_2> | ... | <attribute_n> [Description:
	 * <description>]
	 */
	private String buildToolTip() {
		final List<String> attribute = new ArrayList<String>();
		final FeatureStatus status = feat.getProperty().getFeatureStatus();

		if ((status != FeatureStatus.NORMAL) && (status != FeatureStatus.INDETERMINATE_HIDDEN)) {
			attribute.add("STATUS: " + status);
		}

		if (feat.getStructure().isAbstract()) {
			attribute.add(ABSTRACT);
		} else {
			attribute.add("concrete");
		}

		if (feat.getStructure().isMandatory()) {
			attribute.add(MANDATORY);
		} else {
			attribute.add(OPTIONAL);
		}

		String connectionType = null;
		if (feat.getStructure().isAlternative()) {
			connectionType = "alternative";
		} else if (feat.getStructure().isOr()) {
			connectionType = "or";
		} else if (feat.getStructure().isAnd()) {
			connectionType = "and";
		}
		attribute.add(connectionType + " - connection");

		if (status == FeatureStatus.INDETERMINATE_HIDDEN) {
			attribute.add(HIDDEN_BY_ANCESTOR);
		} else if (feat.getStructure().isHidden()) {
			attribute.add(HIDDEN);
		}

		if (feat.getStructure().hasChildren()) {
			attribute.add(HAS_CHILD_FEATURES);
		} else {
			attribute.add(IS_TERMINAL);
		}

		if (hasConstraints) {
			attribute.add(IS_AFFECTED_BY_CONSTRAINTS);
		}

		final StringBuilder buffer = new StringBuilder();
		buffer.append("attributes: ");
		for (int i = 0; i < (attribute.size() - 1); i++) {
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
		final String featDesc = feat.getProperty().getDescription();
		if ((featDesc != null) && !featDesc.equals("")) {
			buffer.append("\n");
			buffer.append("Description: ");
			buffer.append(featDesc);
		}
	}

	private Parent findConstraints(Parent constraints) {
		if (hasConstraints) {
			for (final IConstraint constr : feat.getStructure().getRelevantConstraints()) {
				constraints.addChild(new Parent(CONSTRAINT, constr.toString()));
			}
		}
		return constraints;
	}

	private Parent findChildFeatures(Parent childFeat) {
		if (feat.getStructure().hasChildren()) {
			for (final IFeatureStructure tempStructure : feat.getStructure().getChildren()) {
				final IFeature temp = tempStructure.getFeature();
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
