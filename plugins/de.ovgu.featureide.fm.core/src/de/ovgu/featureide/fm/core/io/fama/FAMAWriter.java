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
package de.ovgu.featureide.fm.core.io.fama;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Not;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.conversion.ComplexConstraintConverter;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelWriter;

/**
 * Prints feature models in the FaMa format.
 *
 * @deprecated Use {@link FAMAFormat} instead.
 *
 * @author Alexander Knueppel
 */
@Deprecated
public class FAMAWriter extends AbstractFeatureModelWriter {

	/**
	 *
	 * @param feature
	 * @return
	 */
	private String processFeature(IFeature feature) {
		String prefix = "", suffix = "";
		final boolean isAnd = feature.getStructure().isAnd();

		if (!isAnd) {
			if (feature.getStructure().isOr()) {
				prefix += "[1," + feature.getStructure().getChildren().size() + "]{";
			} else if (feature.getStructure().isAlternative()) {
				prefix += "[1,1]{";
			}
			if (!feature.getStructure().getChildren().isEmpty()) {
				suffix = "}";
			}
		}

		final StringBuilder out = new StringBuilder();
		out.append(prefix);

		for (final IFeatureStructure child : feature.getStructure().getChildren()) {
			if (isAnd && !child.isMandatory()) {
				out.append("[" + child.getFeature().getName() + "]");
			} else {
				out.append(child.getFeature().getName());
			}
			out.append(" ");
		}
		out.delete(out.length() - 1, out.length());
		out.append(suffix + ";");
		return out.toString();
	}

	/**
	 *
	 * @param constraint
	 * @return
	 */
	private String processConstraint(IConstraint constraint) {
		org.prop4j.Node node = constraint.getNode().toCNF();

		if (node instanceof And) {
			node = node.getChildren()[0];
		}

		final org.prop4j.Node[] features = node.getChildren();
		final String f1 = features[0].getContainedFeatures().get(0);
		final String f2 = features[1].getContainedFeatures().get(0);

		if ((features[0] instanceof Not) || ((features[0] instanceof Literal) && !((Literal) features[0]).positive)) {
			if ((features[1] instanceof Not) || ((features[1] instanceof Literal) && !((Literal) features[1]).positive)) {
				return f1 + " EXCLUDES " + f2 + ";";
			} else {
				return f1 + " REQUIRES " + f2 + ";";
			}
		} else {
			return f2 + " REQUIRES " + f1 + ";";
		}
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.AbstractObjectWriter#writeToString()
	 */
	@Override
	public String writeToString() {
		// TODO Auto-generated method stub
		final StringBuilder out = new StringBuilder();

		out.append("%Relationships\n");
		for (final IFeature f : object.getFeatures()) {
			if (f.getStructure().hasChildren()) {
				out.append(f.getName() + ": ");
				out.append(processFeature(f) + "\n");
			}
		}

		out.append("\n%Constraints\n");

		for (final IConstraint c : object.getConstraints()) {
			if (ComplexConstraintConverter.isSimple(c.getNode())) {
				out.append(processConstraint(c) + "\n");
			}
		}

		return out.toString();
	}

}
