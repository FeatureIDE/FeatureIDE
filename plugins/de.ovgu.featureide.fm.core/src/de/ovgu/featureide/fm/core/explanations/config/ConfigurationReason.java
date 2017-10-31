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
package de.ovgu.featureide.fm.core.explanations.config;

import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.Reason;

/**
 * A reason of an explanation involving a configuration.
 *
 * @author Timo G&uuml;nther
 */
public class ConfigurationReason extends Reason<SelectableFeature> {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param subject the subject of this reason
	 */
	public ConfigurationReason(SelectableFeature subject) {
		this(subject, null);
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param subject the subject of this reason
	 * @param explanation the containing explanation
	 */
	protected ConfigurationReason(SelectableFeature subject, Explanation<?> explanation) {
		super(subject, explanation);
	}

	@Override
	public Node toNode() {
		return new Literal(NodeCreator.getVariable(getSubject().getFeature()), getSubject().getSelection() == Selection.SELECTED);
	}

	@Override
	protected ConfigurationReason clone() {
		return clone(getExplanation());
	}

	@Override
	protected ConfigurationReason clone(Explanation<?> explanation) {
		return new ConfigurationReason(getSubject(), getExplanation());
	}
}
