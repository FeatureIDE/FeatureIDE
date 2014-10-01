/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.io.velvet;

import java.util.HashSet;
import java.util.LinkedList;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.ExtendedConstraint;
import de.ovgu.featureide.fm.core.ExtendedFeature;
import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.ExtendedFeatureModel.UsedModel;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.AbstractFeatureModelWriter;

/**
 * Writes the feature model to a string in velvet syntax.
 * 
 * @author Sebastian Krieter
 */
public class VelvetFeatureModelWriter extends AbstractFeatureModelWriter {

	private static final String[] SYMBOLS = { "!", "&&", "||", "->", "<->",
			", ", "choose", "atleast", "atmost" };
	private static final String NEWLINE = System.getProperty("line.separator", "\n");
	private StringBuilder sb = new StringBuilder();

	/**
	 * If true an interface will be created. Otherwise it is named "concept"
	 */
	private boolean isInterface = false;
	private ExtendedFeatureModel extFeatureModel = null;
	private final HashSet<String> usedVariables = new HashSet<String>();

	public VelvetFeatureModelWriter(FeatureModel featureModel) {
		setFeatureModel(featureModel);
	}

	public VelvetFeatureModelWriter(FeatureModel featureModel,
			boolean isInterface) {
		this(featureModel);
		this.isInterface = true;
	}

	@Override
	public String writeToString() {
		if (featureModel instanceof ExtendedFeatureModel) {
			extFeatureModel = (ExtendedFeatureModel) featureModel;
		}
		Feature root = featureModel.getRoot();

		if (isInterface) {
			sb.append("cinterface ");
		} else {
			sb.append("concept ");
		}
		sb.append(root.getName());
		if (extFeatureModel != null) {
			usedVariables.clear();
			LinkedList<ExtendedFeatureModel.UsedModel> inheritedModels = new LinkedList<ExtendedFeatureModel.UsedModel>();
			LinkedList<ExtendedFeatureModel.UsedModel> instanceModels = new LinkedList<ExtendedFeatureModel.UsedModel>();
			LinkedList<ExtendedFeatureModel.UsedModel> interfaceModels = new LinkedList<ExtendedFeatureModel.UsedModel>();
			for (UsedModel usedModel : extFeatureModel.getExternalModels().values()) {
				switch (usedModel.getType()) {
				case ExtendedFeature.TYPE_INHERITED:
					inheritedModels.add(usedModel);
					break;
				case ExtendedFeature.TYPE_INSTANCE:
					instanceModels.add(usedModel);
					break;
				case ExtendedFeature.TYPE_INTERFACE:
					interfaceModels.add(usedModel);
					break;
				}
			}
			
			if (!inheritedModels.isEmpty()) {
				sb.append(" : ");
				sb.append(inheritedModels.removeFirst().getModelName());
				for (UsedModel usedModel : inheritedModels) {
					sb.append(", ");
					sb.append(usedModel.getModelName());
				}
			}
			
			if (!instanceModels.isEmpty()) {
				sb.append(NEWLINE);
				sb.append("\tinstance ");
				sb.append(instanceModels.removeFirst());
				for (UsedModel usedModel : instanceModels) {
					sb.append(", ");
					sb.append(usedModel);
				}
			}
			
			if (!interfaceModels.isEmpty()) {
				sb.append(NEWLINE);
				sb.append("\tinterface ");
				sb.append(interfaceModels.removeFirst());
				for (UsedModel usedModel : interfaceModels) {
					sb.append(", ");
					sb.append(usedModel);
				}
			}
		}
		sb.append(" {");
		sb.append(NEWLINE);

		if (extFeatureModel != null) {
			for (Feature child : root.getChildren()) {
				writeUse(child, 1);
			}
			
			for (Constraint constraint : featureModel.getConstraints()) {
				if (((ExtendedConstraint) constraint).getType() == ExtendedFeature.TYPE_INTERN) {
					sb.append("\tconstraint ");
					sb.append(constraint.getNode().toString(SYMBOLS));
					sb.append(";");
					sb.append(NEWLINE);
				}
			}
		} else {
			writeFeatureGroup(root, 1);
			
			for (Constraint constraint : featureModel.getConstraints()) {
				sb.append("\tconstraint ");
				sb.append(constraint.getNode().toString(SYMBOLS));
				sb.append(";");
				sb.append(NEWLINE);
			}
		}
		
		sb.append("}");

		return sb.toString();
	}
	
	private void writeFeatureGroup(Feature curFeature, int depth) {
		if (curFeature.isAnd()) {
			for (Feature feature : curFeature.getChildren()) {
				writeFeature(feature, depth + 1);
			}
		} else if (curFeature.isOr()) {
			writeTab(depth + 1);
			sb.append("someOf {");
			sb.append(NEWLINE);
			for (Feature feature : curFeature.getChildren()) {
				writeFeature(feature, depth + 2);
			}
			writeTab(depth + 1);
			sb.append("}");
			sb.append(NEWLINE);
		} else if (curFeature.isAlternative()) {
			writeTab(depth + 1);
			sb.append("oneOf {");
			sb.append(NEWLINE);
			for (Feature f : curFeature.getChildren()) {
				writeFeature(f, depth + 2);
			}
			writeTab(depth + 1);
			sb.append("}");
			sb.append(NEWLINE);
		}
	}

	private void writeFeature(Feature curFeature, int depth) {
		writeTab(depth);
		if (curFeature.isAbstract()) {
			sb.append("abstract ");
		}
		if (curFeature.isMandatory() && (curFeature.getParent() == null || curFeature.getParent().isAnd())) {
			sb.append("mandatory ");
		}
		sb.append("feature ");
		sb.append(curFeature.getName());

		if (curFeature.getChildrenCount() == 0) {
			sb.append(";");
		} else {
			sb.append(" {");
			sb.append(NEWLINE);
			
			writeFeatureGroup(curFeature, depth);
			
			writeTab(depth);
			sb.append("}");
		}
		sb.append(NEWLINE);
	}
	
	private void writeUse(Feature curFeature, int depth) {
		if (curFeature instanceof ExtendedFeature) {
			ExtendedFeature extFeature = (ExtendedFeature) curFeature;
			
			if (extFeature.getType() == ExtendedFeature.TYPE_INSTANCE 
					|| extFeature.getType() == ExtendedFeature.TYPE_INTERFACE) {
				if (usedVariables.add(extFeature.getExternalModelName())) {
					Feature parent = curFeature.getParent();
					writeTab(depth);
					if (!parent.isRoot()) {
						sb.append("feature ");
						sb.append(parent.getName());
						sb.append(" {");
						sb.append(NEWLINE);
						writeTab(depth + 1);
					}
					sb.append("use ");
					sb.append(extFeature.getExternalModelName());
					sb.append(";");
					sb.append(NEWLINE);
					if (!parent.isRoot()) {
						writeTab(depth);
						sb.append("}");
						sb.append(NEWLINE);
					}
				}
			}
		}
		for (Feature child : curFeature.getChildren()) {
			writeUse(child, depth);
		}
	}

	private void writeTab(int times) {
		for (int i = 0; i < times; i++) {
			sb.append('\t');
		}
	}
}
