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
package de.ovgu.featureide.core.signature.base;

import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.core.signature.ProjectSignatures;

/**
 * Creates new {@link AFeatureData} objects.
 *
 * @author Sebastian Krieter
 */
public class FeatureDataConstructor {

	public static final int TYPE_FOP = 1, TYPE_PP = 2;

	private final ProjectSignatures sigs;
	private final int dataType;

	public FeatureDataConstructor(ProjectSignatures sigs, int dataType) {
		this.sigs = sigs;
		this.dataType = dataType;
	}

	public AFeatureData create(Node constraint, int startLineNumber, int endLineNumber) {
		final AFeatureData data;
		switch (dataType) {
		case TYPE_FOP:
			if (constraint instanceof Literal) {
				data = new FOPFeatureData(sigs.getFeatureID(((Literal) constraint).var.toString()), startLineNumber, endLineNumber);
			} else {
				data = new FOPFeatureData(-1, startLineNumber, endLineNumber);
			}
			data.setConstraint(constraint);
			break;
		case TYPE_PP:
			data = new PreprocessorFeatureData(startLineNumber, endLineNumber);
			data.setConstraint(constraint);
			break;
		default:
			data = null;
		}
		return data;
	}

	public AFeatureData create(int id, int startLineNumber, int endLineNumber) {
		final AFeatureData data;
		switch (dataType) {
		case TYPE_FOP:
			data = new FOPFeatureData(id, startLineNumber, endLineNumber);
			data.setConstraint(new Literal(sigs.getFeatureName(id)));
			break;
		case TYPE_PP:
			data = new PreprocessorFeatureData(startLineNumber, endLineNumber);
			data.setConstraint(new Literal(sigs.getFeatureName(id)));
			break;
		default:
			data = null;
		}
		return data;
	}

	public ProjectSignatures getSigs() {
		return sigs;
	}

}
