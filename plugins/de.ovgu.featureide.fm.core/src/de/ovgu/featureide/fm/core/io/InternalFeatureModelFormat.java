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
package de.ovgu.featureide.fm.core.io;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;

/**
 * Writes feature models in an internal, simplified format.
 *
 * @author Sebastian Krieter
 */
public class InternalFeatureModelFormat extends APersistentFormat<IFeatureModel> implements IFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + InternalFeatureModelFormat.class.getSimpleName();

	private static final String[] SYMBOLS = { "!", "&&", "||", "->", "<->", ", ", "choose", "atleast", "atmost" };
	private static final String NEWLINE = System.getProperty("line.separator", "\n");
	private final StringBuilder sb = new StringBuilder();

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String write(IFeatureModel object) {
		final IFeatureStructure root = object.getStructure().getRoot();
		if (root == null) {
			return "";
		}
		sb.delete(0, sb.length());

		sb.append(root.getFeature().getName());
		sb.append("{");
		sb.append(NEWLINE);

		writeFeatureGroup(root);

		for (final IConstraint constraint : object.getConstraints()) {
			sb.append(constraint.getNode().toString(SYMBOLS));
			sb.append(NEWLINE);
		}

		sb.append("}");

		return sb.toString();
	}

	private void writeFeatureGroup(IFeatureStructure root) {
		if (root.isAnd()) {
			for (final IFeatureStructure feature : root.getChildren()) {
				writeFeature(feature);
			}
		} else if (root.isOr()) {
			sb.append("o{");
			sb.append(NEWLINE);
			for (final IFeatureStructure feature : root.getChildren()) {
				writeFeature(feature);
			}
			sb.append("}");
			sb.append(NEWLINE);
		} else if (root.isAlternative()) {
			sb.append("x{");
			sb.append(NEWLINE);
			for (final IFeatureStructure f : root.getChildren()) {
				writeFeature(f);
			}
			sb.append("}");
			sb.append(NEWLINE);
		}
	}

	private void writeFeature(IFeatureStructure feature) {
		if (feature.isAbstract()) {
			sb.append("a ");
		}
		if (feature.isMandatory() && ((feature.getParent() == null) || feature.getParent().isAnd())) {
			sb.append("m ");
		}
		sb.append(feature.getFeature().getName());
		final String description = feature.getFeature().getProperty().getDescription();
		final boolean hasDescription = (description != null) && !description.isEmpty();

		if ((feature.getChildrenCount() != 0) || hasDescription) {
			sb.append(" {");
			sb.append(NEWLINE);
			if (hasDescription) {
				sb.append("d\"");
				sb.append(description.replace("\"", "\\\""));
				sb.append("\";");
				sb.append(NEWLINE);
			}

			writeFeatureGroup(feature);

			sb.append("}");
		}
		sb.append(NEWLINE);
	}

	@Override
	public boolean supportsContent(CharSequence content) {
		return true;
	}

	@Override
	public String getSuffix() {
		return "";
	}

	@Override
	public InternalFeatureModelFormat getInstance() {
		return new InternalFeatureModelFormat();
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public String getName() {
		return "FeatureIDE Internal";
	}

}
