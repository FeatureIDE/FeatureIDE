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

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.conversion.ComplexConstraintConverter;
import de.ovgu.featureide.fm.core.io.AFeatureModelFormat;

/**
 * Prints feature models in the FaMa format.
 *
 * @author Alexander Knueppel
 * @author Sebastian Krieter
 */
public class FAMAFormat extends AFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + FAMAFormat.class.getSimpleName();

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

	@Override
	public String write(IFeatureModel featureModel) {
		final StringBuilder out = new StringBuilder();

		out.append("%Relationships\n");
		for (final IFeature f : featureModel.getFeatures()) {
			if (f.getStructure().hasChildren()) {
				out.append(f.getName() + ": ");
				out.append(processFeature(f) + "\n");
			}
		}

		out.append("\n%Constraints\n");

		for (final IConstraint c : featureModel.getConstraints()) {
			if (ComplexConstraintConverter.isSimple(c.getNode())) {
				out.append(processConstraint(c) + "\n");
			}
		}

		return out.toString();
	}

	@Override
	public String getSuffix() {
		return "fama";
	}

	@Override
	public FAMAFormat getInstance() {
		return this;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public String getName() {
		return "FAMA";
	}

}
