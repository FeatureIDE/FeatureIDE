/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io.velvet;

import java.io.File;
import java.io.FilenameFilter;
import java.util.Collection;
import java.util.LinkedList;
import java.util.Map.Entry;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.prop4j.And;
import org.prop4j.Choose;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.base.impl.MultiConstraint;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel.UsedModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModelFactory;
import de.ovgu.featureide.fm.core.constraint.Equation;
import de.ovgu.featureide.fm.core.constraint.FeatureAttribute;
import de.ovgu.featureide.fm.core.constraint.Reference;
import de.ovgu.featureide.fm.core.constraint.ReferenceType;
import de.ovgu.featureide.fm.core.constraint.RelationOperator;
import de.ovgu.featureide.fm.core.constraint.WeightedTerm;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;
import de.ovgu.featureide.fm.core.io.velvet.VelvetParser.AttribNumExprContext;
import de.ovgu.featureide.fm.core.io.velvet.VelvetParser.FeatureContext;
import de.ovgu.featureide.fm.core.io.velvet.VelvetParser.NonFeatureDefinitionContext;

//import de.ovgu.featureide.fm.core.io.velvet.VelvetParser.ConceptContext;

/**
 * TODO description
 *
 * @author mgrave
 * @author Oleksandr Kudriavchenko
 */
public class VelvetVisitorImpl extends VelvetBaseVisitor<Void> {

	private final IVelvetFeatureModelFormat data;
	// private final SimpleVelvetFeatureModelFormat data;
	private final MultiFeatureModelFactory factory;
	private Node RHS;
	private Node LHS;
	private RelationOperator relationOperator = null;
	private IFeature currentParentFeature = null;
	private LinkedList<WeightedTerm> weightedTerms;
	int degree = 0;
	private String equationID = null;
	private boolean useLongNames;

	/**
	 * @param velvetFeatureModelFormat
	 */
	public VelvetVisitorImpl(IVelvetFeatureModelFormat data) {

		factory = MultiFeatureModelFactory.getInstance();
		useLongNames = false;
		if (data instanceof VelvetFeatureModelFormat) {
			this.data = (VelvetFeatureModelFormat) data;
		} else if (data instanceof SimpleVelvetFeatureModelFormat) {
			this.data = (SimpleVelvetFeatureModelFormat) data;
		} else {
			this.data = null;
			return;
		}

	}

	@Override
	public Void visitVelvetModel(VelvetParser.VelvetModelContext ctx) {

		if (ctx.imp() != null) {
			useLongNames = true;
			visitImp(ctx.imp());
		}
		if (ctx.concept() != null) {
			visitConcept(ctx.concept());

		} else if (ctx.cinterface() != null) {
			data.getExtFeatureModel().setInterface(true);
			visitCinterface(ctx.cinterface());
		}
		if (!data.getIsUsedAsAPI()) {
			final IFeatureModelFactory mappingModelFactory = DefaultFeatureModelFactory.getInstance();
			final IFeatureModel mappingModel = mappingModelFactory.create();
			final IFeatureStructure rootFeature = mappingModelFactory.createFeature(mappingModel, "MPL").getStructure();
			rootFeature.setAnd();
			rootFeature.setAbstract(true);
			rootFeature.setMandatory(true);

			final LinkedList<String> possibleProjects = new LinkedList<>();
			final IProject[] projects = ResourcesPlugin.getWorkspace().getRoot().getProjects();
			for (int i = 0; i < projects.length; i++) {
				final IProject project = projects[i];
				if (project.isAccessible()) {
					possibleProjects.add(project.getName());
				}
			}

			for (final Entry<String, UsedModel> parameter : data.getExtFeatureModel().getExternalModels().entrySet()) {
				if (parameter.getValue().getType() == MultiFeature.TYPE_INTERFACE) {
					final IFeatureStructure parameterFeature = mappingModelFactory.createFeature(mappingModel, parameter.getKey()).getStructure();
					parameterFeature.setOr();
					parameterFeature.setAbstract(true);
					parameterFeature.setMandatory(true);
					rootFeature.addChild(parameterFeature);

					for (final String projectName : possibleProjects) {
						final IFeatureStructure projectFeature =
							mappingModelFactory.createFeature(mappingModel, parameterFeature.getFeature().getName() + "." + projectName).getStructure();
						projectFeature.setAbstract(false);
						projectFeature.setMandatory(false);
						parameterFeature.addChild(projectFeature);
					}
				}
			}
			mappingModel.getStructure().setRoot(rootFeature);
			data.getExtFeatureModel().setMappingModel(mappingModel);
		}
		return null;
	}

	@Override
	public Void visitConcept(VelvetParser.ConceptContext ctx) {

		if (ctx.ID() != null) {
			data.setExtFeatureModelName(ctx.ID().getText());
			final MultiFeature rootFeature = (MultiFeature) factory.createFeature(data.getExtFeatureModel(), data.getExtFeatureModelName());
			rootFeature.getStructure().setAbstract(true);
			rootFeature.getStructure().setMandatory(true);
			data.getExtFeatureModel().addFeature(rootFeature);
			data.getExtFeatureModel().getStructure().setRoot(rootFeature.getStructure());
			currentParentFeature = rootFeature;
		}

		if (ctx.conceptBaseExt() != null) {
			useLongNames = true;
			visitConceptBaseExt(ctx.conceptBaseExt());

		}
		if (ctx.interfaceImports() != null) {
			useLongNames = true;
			visitInterfaceImports(ctx.interfaceImports());
		}
		if (ctx.instanceImports() != null) {
			useLongNames = true;
			visitInstanceImports(ctx.instanceImports());
		}
		if (ctx.definitions() != null) {
			visitDefinitions(ctx.definitions());
		}
		return null;
	}

	@Override
	public Void visitImp(VelvetParser.ImpContext ctx) {
		for (final ParseTree imp : ctx.name()) {
			data.getExtFeatureModel().addImport(imp.getText());
		}
		return null;
	}

	@Override
	public Void visitCinterface(VelvetParser.CinterfaceContext ctx) {
		if (ctx.ID() != null) {
			data.setExtFeatureModelName(ctx.ID().getText());
			final MultiFeature rootFeature = (MultiFeature) factory.createFeature(data.getExtFeatureModel(), data.getExtFeatureModelName());
			rootFeature.getStructure().setAbstract(true);
			rootFeature.getStructure().setMandatory(true);
			data.getExtFeatureModel().addFeature(rootFeature);
			data.getExtFeatureModel().getStructure().setRoot(rootFeature.getStructure());
			currentParentFeature = rootFeature;
		}
		if (ctx.conceptBaseExt() != null) {
			visitConceptBaseExt(ctx.conceptBaseExt());
		}
		if (ctx.definitions() != null) {
			visitDefinitions(ctx.definitions());
		}
		return null;
	}

	@Override
	public Void visitConceptBaseExt(VelvetParser.ConceptBaseExtContext ctx) {
		for (final TerminalNode id : ctx.ID()) {
			final String parentModelName = id.getText();
			final IFeatureModel fm = getExternalFeatureModel(parentModelName);
			if (fm == null) {
				return null;
			}
			if (!data.getExtFeatureModel().addInheritance(parentModelName, parentModelName, null)) {
				reportWarning("THE_PARENT_MODEL" + parentModelName + "IS_ALREADY_USED_");
				return null;
			}
			addExternalFeatures(fm, parentModelName, data.getExtFeatureModel().getStructure().getRoot(), MultiFeature.TYPE_INHERITED);
		}
		return null;
	}

	@Override
	public Void visitInstanceImports(VelvetParser.InstanceImportsContext ctx) {
		int i = 0;
		for (final TerminalNode id : ctx.ID()) {
			final String interfaceName = id.getText();
			final String varName = ctx.name(i).getText();
			i++;
			if (checkExternalModelFile(interfaceName)) {
				if (!data.getExtFeatureModel().addInstance(interfaceName, varName, null)) {
					reportWarning("THE_VARIABLE_NAME " + varName + " IS_ALREADY_IN_USE_");
				}
			}
		}
		return null;
	}

	@Override
	public Void visitInterfaceImports(VelvetParser.InterfaceImportsContext ctx) {
		int i = 0;
		for (final TerminalNode id : ctx.ID()) {
			final String interfaceName = id.getText();
			final String varName = ctx.name(i).getText();
			i++;
			if (checkExternalModelFile(interfaceName)) {
				if (!data.getExtFeatureModel().addInterface(interfaceName, varName, null)) {
					reportWarning("THE_VARIABLE_NAME " + varName + " IS_ALREADY_IN_USE_");
				}
			}
		}
		return null;
	}

	private boolean checkExternalModelFile(String curNode) {
		if (data.getLocalSearch()) {
			if (localSearch(curNode) == null) {
				reportWarning(String.format("No model for %s could be found.", curNode));
				return false;
			}
			return true;
		}
		if (getExternalModelFile(curNode) == null) {
			reportWarning(String.format("No model for %s could be found.", curNode));
			return false;
		}
		return true;
	}

	@Override
	public Void visitDefinitions(VelvetParser.DefinitionsContext ctx) {
		if (ctx.definition() != null) {
			visitDefinition(ctx.definition());
		}
		return null;
	}

	@Override
	public Void visitDefinition(VelvetParser.DefinitionContext ctx) {

		final IFeature parent = currentParentFeature;
		for (final FeatureContext feature : ctx.feature()) {
			currentParentFeature = parent;
			visitFeature(feature);
		}

		if (ctx.featureGroup() != null) {
			currentParentFeature = parent;
			visitFeatureGroup(ctx.featureGroup());
		}

		for (final NonFeatureDefinitionContext nonFeatureDef : ctx.nonFeatureDefinition()) {
			currentParentFeature = parent;
			visitNonFeatureDefinition(nonFeatureDef);
		}

		currentParentFeature = parent;

		return null;
	}

	@Override
	public Void visitNonFeatureDefinition(VelvetParser.NonFeatureDefinitionContext ctx) {

		if (ctx.constraint() != null) {
			visitConstraint(ctx.constraint());
		} else if (ctx.attribute() != null) {
			visitAttribute(ctx.attribute());
		} else if (ctx.description() != null) {
			visitDescription(ctx.description());
		} else if (ctx.use() != null) {
			visitUse(ctx.use());
		}

		return null;
	}

	private IFeatureModel getInterfaceFeatureModel(String curNode) {
		final File modelFile = getInterfaceModelFile(curNode);
		if (modelFile == null) {
			return null;
		}
		return readModel(modelFile, curNode);
	}

	private IFeatureModel getExternalFeatureModel(String curNode) {
		final File modelFile = getExternalModelFile(curNode);
		if (modelFile == null) {
			reportWarning(String.format("No model for %s could be found.", curNode));
			return null;
		}
		return readModel(modelFile, curNode);
	}

	private IFeatureModel readModel(File modelFile, String curNode) {
		IFeatureModel fm = null;
		if (data.getIsUsedAsAPI()) {
			fm = readExternalModelFileAPI(modelFile);
		} else {
			fm = readExternalModelFile(modelFile);
		}
		if (fm == null) {
			reportWarning(String.format("External model for %s could not be read.", curNode));
			return null;
		}
		return fm;
	}

	private IFeatureModel readExternalModelFile(File file) {
		return FeatureModelManager.load(file.toPath());
	}

	private IFeatureModel readExternalModelFileAPI(File file) {
		final IFeatureModel fm = new MultiFeatureModelFactory().create();
		fm.setSourceFile(file.toPath());
		SimpleFileHandler.load(file.toPath(), fm, FMFormatManager.getInstance());
		return fm;
	}

	private File getExternalModelFile(String name) {
		if (!data.getExtFeatureModel().getImports().isEmpty() && !data.getIsUsedAsAPI()) {
			for (final String path : data.getExtFeatureModel().getImports()) {
				final IProject project = data.getProject();
				if (!path.endsWith(name)) {
					continue;
				}
				if (project != null) {
					IResource res = project.getFile(path + ".xml");
					if ((res != null) && res.exists()) {
						return res.getLocation().toFile();
					}
					res = project.getFile(path + ".velvet");
					if ((res != null) && res.exists()) {
						return res.getLocation().toFile();
					}
				}
			}
		}

		if (data.getLocalSearch() || data.getIsUsedAsAPI()) {
			return localSearch(name);
		}
		File returnFile = null;

		// local search
		IProject project = data.getProject();
		if (project != null) {
			for (int i = 0; i < data.getPaths().length; i++) {
				final IResource res = project.findMember(String.format(data.getPaths()[i], name));
				if (res != null) {
					returnFile = res.getLocation().toFile();
					if (returnFile.equals(data.getFeatureModelFile())) {
						returnFile = null;
					} else {
						break;
					}
				}
			}
		}

		// external search
		if (returnFile == null) {
			// if could not get current project or could not find file in current
			// project assume the name is the project name
			project = ResourcesPlugin.getWorkspace().getRoot().getProject(name);
			if (project.isAccessible()) {
				returnFile = project.getFile("model.xml").getLocation().toFile();
				if (returnFile.equals(data.getFeatureModelFile())) {
					return null;
				}
			} else {
				Logger.logWarning(String.format("Project %s is not accessible.", name));
			}
		}
		if ((returnFile == null) || !returnFile.exists() || !returnFile.canRead()) {
			return null;
		}
		return returnFile;
	}

	private File getInterfaceModelFile(String name) {
		if (data.getLocalSearch()) {
			return localSearch(name);
		}
		File returnFile = null;
		final IProject project = data.getProject();
		if (project != null) {
			final IResource res = project.findMember(String.format("Interfaces/%s.velvet", name));
			if (res != null) {
				returnFile = res.getLocation().toFile();
			}
		}
		return returnFile;
	}

	private File localSearch(final String name) {
		if (data.getFeatureModelFile() != null) {
			final File searchDir = new File(data.getFeatureModelFile().getParentFile(), "MPL");
			if (searchDir != null) {
				final File[] files = searchDir.listFiles(new FilenameFilter() {

					@Override
					public boolean accept(File dir, String fileName) {
						final int index = fileName.lastIndexOf('.');
						return (index > 0) && fileName.substring(0, index).equals(name) && fileName.substring(index + 1).matches("xml|velvet");
					}
				});
				if ((files != null) && (files.length > 0)) {
					return files[0];
				}
			}
		}
		return null;
	}

	@Override
	public Void visitUse(VelvetParser.UseContext ctx) {

		final String varName = ctx.name().getText();
		final IFeature parent = currentParentFeature;
		final UsedModel usedModel = data.getExtFeatureModel().getExternalModel(varName);
		if (usedModel == null) {
			reportWarning(String.format("No variable with the name %s found.", varName));
			return null;
		}
		switch (usedModel.getType()) {
		case MultiFeature.TYPE_INTERFACE:
			final IFeatureModel interfaceModel = getInterfaceFeatureModel(usedModel.getModelName());
			if (interfaceModel == null) {
				return null;
			}
			addExternalFeatures(interfaceModel, varName, parent.getStructure(), MultiFeature.TYPE_INTERFACE);
			break;
		case MultiFeature.TYPE_INSTANCE:
			final IFeatureModel instanceModel = getExternalFeatureModel(usedModel.getModelName());
			if (instanceModel == null) {
				return null;
			}
			addExternalFeatures(instanceModel, varName, parent.getStructure(), MultiFeature.TYPE_INSTANCE);
			break;
		default: //
			reportWarning(String.format("The variable with the name %s is no interface or instance.", varName));
		}

		return null;
	}

	private void addExternalFeatures(IFeatureModel sourceModel, String sourceModelName, IFeatureStructure targetParentFeature, int type) {
		if (sourceModel instanceof MultiFeatureModel) {
			for (final UsedModel usedModel : ((MultiFeatureModel) sourceModel).getExternalModels().values()) {
				data.getExtFeatureModel().addExternalModel(new UsedModel(usedModel, sourceModelName));
			}
		}
		final UsedModel usedModel = data.getExtFeatureModel().getExternalModel(sourceModelName);
		if (usedModel != null) {
			usedModel.setPrefix(targetParentFeature.getFeature().getName() + "." + sourceModelName);
		}
		final IFeatureStructure instanceRoot = sourceModel.getStructure().getRoot();
		String connectorName = "";
		if (type == MultiFeature.TYPE_INHERITED) {
			connectorName = targetParentFeature.getFeature().getName();
		} else {
			connectorName = (targetParentFeature.isRoot() && targetParentFeature.getFeature().getName().equals(sourceModelName))
				? targetParentFeature.getFeature().getName() : targetParentFeature.getFeature().getName() + "." + sourceModelName;
		}
		final MultiFeature connector = addFeature(targetParentFeature.getFeature(), connectorName, true, true, instanceRoot.isHidden());
		connector.setType(type);
		connector.setExternalModelName(sourceModelName);
		if (instanceRoot.isAlternative()) {
			connector.getStructure().setAlternative();
		} else if (instanceRoot.isOr()) {
			connector.getStructure().setOr();
		}

		copyChildnodes(data.getExtFeatureModel(), connector.getStructure(), instanceRoot, sourceModelName, connectorName, type);

		for (final IConstraint constraint : sourceModel.getConstraints()) {
			final Node constraintParent_ID_Value = constraint.getNode();

			final int IDValue_Index = constraintParent_ID_Value.getChildren().length - 1;
			final Node constraintID_Value = constraintParent_ID_Value.getChildren()[IDValue_Index];
			final int Value_Index = constraintID_Value.getChildren().length - 1;
			final Node constraintValue = constraintID_Value.getChildren()[Value_Index];

			// Update parent's name
			updateConstraintNode(constraintParent_ID_Value.getChildren()[0], connectorName, instanceRoot.getFeature().getName(), data.getExtFeatureModel());
			// Update constraint's Value (node itself)
			updateConstraintNode(constraintValue, connectorName, instanceRoot.getFeature().getName(), data.getExtFeatureModel());

			final MultiConstraint newConstraint = (MultiConstraint) factory.createConstraint(data.getExtFeatureModel(), constraintParent_ID_Value);
			newConstraint.setType(type);
			data.getExtFeatureModel().addConstraint(newConstraint);
		}
	}

	private static void updateConstraintNode(Node curNode, String parentModelname, String rootName, IFeatureModel targetModel) {
		if (curNode instanceof Literal) {
			final Literal literal = (Literal) curNode;
			if (literal.var.equals(rootName)) {
				literal.var = parentModelname;
			} else {
				// if fully qualified name
				IFeature feature = targetModel.getFeature(literal.var.toString().replace(rootName, parentModelname));
				if (feature == null) {
					// else
					feature = targetModel.getFeature(parentModelname + "." + literal.var.toString());
				}
				literal.var = feature.getName();
			}
		} else {
			for (final Node child : curNode.getChildren()) {
				updateConstraintNode(child, parentModelname, rootName, targetModel);
			}
		}
	}

	private void copyChildnodes(final MultiFeatureModel targetModel, final IFeatureStructure targetParentNode, final IFeatureStructure sourceParentNode,
			final String parentModelName, final String targetParentName, final int type) {
		for (final IFeatureStructure sourceChildStructure : sourceParentNode.getChildren()) {
			final MultiFeature feature;
			if (data.isVelvetImport()) {
				feature = (MultiFeature) factory.createFeature(targetModel, sourceChildStructure.getFeature().getName());
			} else {
				final String shortName = sourceChildStructure.getFeature().getName().replace(sourceParentNode.getFeature().getName() + ".", "");
				feature = (MultiFeature) factory.createFeature(targetModel, targetParentName + "." + shortName);
			}
			final IFeatureStructure targetChildStructure = feature.getStructure();
			targetChildStructure.setMandatory(sourceChildStructure.isMandatory());
			targetChildStructure.setAbstract(sourceChildStructure.isAbstract());
			targetChildStructure.setHidden(sourceChildStructure.isHidden());
			feature.setExternalModelName(parentModelName);
			targetChildStructure.setAND(sourceChildStructure.isAnd());
			targetChildStructure.setMultiple(sourceChildStructure.isMultiple());
			if (sourceChildStructure.isOr()) {
				targetChildStructure.setOr();
			}

			targetModel.addFeature(feature);
			targetParentNode.addChild(targetChildStructure);
			feature.setType(type);

			if (sourceChildStructure.hasChildren()) {
				copyChildnodes(targetModel, targetChildStructure, sourceChildStructure, parentModelName, feature.getName(), type);
			}
		}
	}

	/**
	 * @param string
	 */
	private void reportWarning(String message) {
		Logger.logWarning(message + ((data.getFeatureModelFile() != null) ? "IN_FILE" + data.getFeatureModelFile() : ""));
	}

	@Override
	public Void visitFeature(VelvetParser.FeatureContext ctx) {
		String featureName = ctx.name().getText();
		final boolean isMandatory = ctx.MANDATORY() != null;
		final boolean isAbstract = ctx.ABSTRACT() != null;
		if (!data.getExtFeatureModel().isInterface()) {

			if (data.isVelvetImport() || currentParentFeature.getStructure().isRoot()
				|| (!useLongNames && featureName.startsWith(currentParentFeature.getName()))) {
				featureName = ctx.name().getText();
			} else {
				featureName = currentParentFeature.getName() + "." + featureName;
			}
		}
		final MultiFeature newFeature = addFeature(currentParentFeature, featureName, isMandatory, isAbstract, false);
		if (ctx.definitions() != null) {
			currentParentFeature = newFeature;
			visitDefinitions(ctx.definitions());
		}
		return null;
	}

	private MultiFeature addFeature(final IFeature parent, final String featureName, final boolean isMandatory, final boolean isAbstract,
			final boolean isHidden) {
		final MultiFeature newFeature = (MultiFeature) factory.createFeature(data.getExtFeatureModel(), featureName);
		newFeature.getStructure().setMandatory(isMandatory);
		newFeature.getStructure().setAbstract(isAbstract);
		newFeature.getStructure().setHidden(isHidden);
		final IFeature orgFeature = data.getExtFeatureModel().getFeature(featureName);
		if ((orgFeature != null) && (orgFeature instanceof MultiFeature)) {
			return (MultiFeature) orgFeature;
		} else {
			data.getExtFeatureModel().addFeature(newFeature);
			parent.getStructure().addChild(newFeature.getStructure());
			newFeature.setNewDefined(true);
			return newFeature;
		}
	}

	@Override
	public Void visitFeatureGroup(VelvetParser.FeatureGroupContext ctx) {
		if (ctx.groupType() != null) {
			visitGroupType(ctx.groupType());
		}
		for (final FeatureContext feature : ctx.feature()) {
			visitFeature(feature);
		}
		return null;
	}

	@Override
	public Void visitGroupType(VelvetParser.GroupTypeContext ctx) {
		if (ctx.SOMEOF() != null) {
			currentParentFeature.getStructure().setOr();
		} else if (ctx.ONEOF() != null) {
			currentParentFeature.getStructure().setAlternative();
		} else {
			currentParentFeature.getStructure().setAnd();
		}
		return null;
	}

	@Override
	public Void visitConstraint(VelvetParser.ConstraintContext ctx) {
		if (ctx.constraintDefinition() != null) {
			visitConstraintDefinition(ctx.constraintDefinition());
			if (ctx.ID() != null) {
				RHS = new Equals(new Literal(ctx.ID().getText()), RHS);
			}
			RHS = new Implies(new Literal(currentParentFeature.getName()), RHS);
			data.getExtFeatureModel().addConstraint(factory.createConstraint(data.getExtFeatureModel(), RHS));
			RHS = null;
		} else if (ctx.attributeConstraint() != null) {
			equationID = null;
			if (ctx.ID() != null) {
				equationID = ctx.ID().getText();
			}
			visitAttributeConstraint(ctx.attributeConstraint());
		}
		return null;
	}

	private static WeightedTerm createTerm(final int weight, final boolean rightSide, final boolean minus, final Reference reference) {
		boolean positive = weight >= 0;
		if (rightSide ^ minus) {
			positive = !positive;
		}
		return new WeightedTerm(Math.abs(weight), positive, reference);
	}

	@Override
	public Void visitConstraintDefinition(VelvetParser.ConstraintDefinitionContext ctx) {

		// RHS = null;
		int operator = 0;
		for (int i = 0;; i++) {
			if (ctx.constraintOperand(i) == null) {
				break;
			}
			if (LHS == null) {
				visitConstraintOperand(ctx.constraintOperand(i));// LHS = result
			}
			switch (operator) {
			case VelvetParser.OP_AND:
				LHS = new And(RHS, LHS);
				break;
			case VelvetParser.OP_OR:
				LHS = new Or(RHS, LHS);
				break;
			case VelvetParser.OP_XOR:
				LHS = new Choose(1, RHS, LHS);
				break;
			case VelvetParser.OP_IMPLIES:
				LHS = new Implies(RHS, LHS);
				break;
			case VelvetParser.OP_EQUIVALENT:
				LHS = new Equals(RHS, LHS);
				break;
			default:
				break;
			}
			if (ctx.binaryOp(i) != null) {
				operator = ctx.binaryOp(i).getStart().getType();
			}
			RHS = LHS;
			LHS = null;
		}
		return null;

	}

	@Override
	public Void visitConstraintOperand(VelvetParser.ConstraintOperandContext ctx) {
		// put result in lhs
		final Node tempRHS = RHS;
		if (ctx.constraintDefinition() != null) {
			RHS = null;// clean RHS, so it doesnt mess with visitConstraintDefinition
			visitConstraintDefinition(ctx.constraintDefinition());
			LHS = RHS;
			RHS = tempRHS;// restoring previous RHS
		} else if (ctx.name() != null) {
			LHS = new Literal(ctx.name().getText());
		}
		if (ctx.unaryOp(0) != null) {// only "not" is currently present in the grammar
			LHS = new Not(LHS);
		}
		return null;
	}

	@Override
	public Void visitAttribute(VelvetParser.AttributeContext ctx) {

		String name;
		if (ctx.floatAttribute() != null) {
			// pass
		} else if (ctx.intAttribute() != null) {
			name = ctx.intAttribute().name().getText();
			data.getExtFeatureModel().addAttribute(currentParentFeature.getName(), name, Integer.parseInt(ctx.intAttribute().INT().getText()));
		} else if (ctx.boolAttribute() != null) {
			name = ctx.boolAttribute().name().getText();
			data.getExtFeatureModel().addAttribute(currentParentFeature.getName(), name, Boolean.parseBoolean(ctx.boolAttribute().BOOLEAN().getText()));
		} else if (ctx.stringAttribute() != null) {
			name = ctx.stringAttribute().name().getText();
			data.getExtFeatureModel().addAttribute(currentParentFeature.getName(), name, ctx.stringAttribute().STRING().getText());
		} else {
			reportSyntaxError(ctx);
		}
		return null;

	}

	private void reportSyntaxError(ParserRuleContext context) throws RecognitionException {
		// maybe it should be in SimpleVelvetModelFormat
		final RecognitionException ex = new RecognitionException(null, null, context);
		throw ex;
	}

	@Override
	public Void visitAttributeConstraint(VelvetParser.AttributeConstraintContext ctx) {
		weightedTerms = new LinkedList<>();
		weightedTerms.clear();
		degree = 0;
		relationOperator = null;
		if (!ctx.attribNumExpr().isEmpty()) {
			final AttribNumExprContext one = ctx.attribNumExpr().getFirst();
			final AttribNumExprContext two = ctx.attribNumExpr().getLast();
			visitAttribNumExpr(one);
			if (ctx.attribRelation() != null) {
				visitAttribRelation(ctx.attribRelation());
			}
			visitAttribNumExpr(two);

		}
		final Equation equation = new Equation(weightedTerms, relationOperator, degree);
		data.getExtFeatureModel().addAttributeConstraint(equation);
		return null;
	}

	@Override
	public Void visitAttribNumExpr(VelvetParser.AttribNumExprContext ctx) {
		boolean minus = false;
		int i = 0;
		do {
			if ((ctx.attribOperator(i - 1) != null) && (i > 0)) {
				if (ctx.attribOperator(i - 1).PLUS() != null) {
					minus = false;
				} else if (ctx.attribOperator(i - 1).MINUS() != null) {
					minus = true;
				}
			}
			if (ctx.attribNumInstance(i).INT() != null) {
				final int value = Integer.parseInt(ctx.attribNumInstance(i).INT().getText());
				if ((relationOperator == null) ^ minus) {
					degree -= value;
				} else {
					degree += value;
				}
				weightedTerms.add(createTerm(value, relationOperator != null, minus,
						new Reference(currentParentFeature.getName(), ReferenceType.FEATURE, "attributeName")));
			} else if (ctx.attribNumInstance(i).name() != null) {
				final String attributeName = ctx.attribNumInstance(i).name().getText();
				final Collection<FeatureAttribute<Integer>> attributes = data.getExtFeatureModel().getIntegerAttributes().getAttributes(attributeName);

				if (attributes == null) {
					// throw new UnsupportedModelException(ctx.getStart().getLine() + ":" + "NO_SUCH_ATTRIBUTE_DEFINED", ctx.getStart().getLine());
					return null;
				}
				for (final FeatureAttribute<Integer> attr : attributes) {
					weightedTerms.add(createTerm(attr.getValue(), relationOperator != null, minus,
							new Reference(attr.getFeatureName(), ReferenceType.FEATURE, attributeName)));
				}
			}
			i++;
		} while (i <= ctx.attribOperator().size());

		return null;
	}

	@Override
	public Void visitDescription(VelvetParser.DescriptionContext ctx) {
		return null;
	}

	@Override
	public Void visitAttribOperator(VelvetParser.AttribOperatorContext ctx) {
		return null;
	}

	@Override
	public Void visitAttribNumInstance(VelvetParser.AttribNumInstanceContext ctx) {
		return null;
	}

	@Override
	public Void visitName(VelvetParser.NameContext ctx) {
		return null;
	}

	@Override
	public Void visitIntAttribute(VelvetParser.IntAttributeContext ctx) {
		return null;
	}

	@Override
	public Void visitFloatAttribute(VelvetParser.FloatAttributeContext ctx) {
		return null;
	}

	@Override
	public Void visitStringAttribute(VelvetParser.StringAttributeContext ctx) {
		return null;
	}

	@Override
	public Void visitBoolAttribute(VelvetParser.BoolAttributeContext ctx) {
		return null;
	}

	@Override
	public Void visitUnaryOp(VelvetParser.UnaryOpContext ctx) {
		return null;
	}

	@Override
	public Void visitBinaryOp(VelvetParser.BinaryOpContext ctx) {

		return null;
	}

	@Override
	public Void visitAttribRelation(VelvetParser.AttribRelationContext ctx) {
		if (ctx.ATTR_OP_EQUALS() != null) {
			relationOperator = RelationOperator.EQUAL;

		} else if (ctx.ATTR_OP_GREATER_EQ() != null) {
			relationOperator = RelationOperator.GREATER_EQUAL;

		} else if (ctx.ATTR_OP_LESS_EQ() != null) {
			relationOperator = RelationOperator.LESS_EQUAL;

		}
		return null;
	}

}
