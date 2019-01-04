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
package de.ovgu.featureide.fm.core.io.velvet;

import static de.ovgu.featureide.fm.core.localization.StringTable.ILLEGAL_SYNTAX_IN_LINE;
import static de.ovgu.featureide.fm.core.localization.StringTable.IN_FILE;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_ALREADY_IN_USE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.IS_ALREADY_USED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.NO_SUCH_ATTRIBUTE_DEFINED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_PARENT_MODEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_VARIABLE_NAME;
import static de.ovgu.featureide.fm.core.localization.StringTable.USE;
import static java.lang.String.format;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.Map.Entry;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.CommonErrorNode;
import org.antlr.runtime.tree.Tree;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.prop4j.And;
import org.prop4j.Choose;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.ModelMarkerHandler;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.ExtendedConstraint;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModel.UsedModel;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.constraint.Equation;
import de.ovgu.featureide.fm.core.constraint.FeatureAttribute;
import de.ovgu.featureide.fm.core.constraint.Reference;
import de.ovgu.featureide.fm.core.constraint.ReferenceType;
import de.ovgu.featureide.fm.core.constraint.RelationOperator;
import de.ovgu.featureide.fm.core.constraint.WeightedTerm;
import de.ovgu.featureide.fm.core.io.AFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.SimpleFileHandler;

/**
 * Reads / Writes feature models in the Velvet format.
 *
 * @author Sebastian Krieter
 * @author Matthias Strauss
 * @author Reimar Schroeter
 */
public class VelvetFeatureModelFormat extends AFeatureModelFormat {

	public static boolean IS_USED_AS_API = false;
	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + VelvetFeatureModelFormat.class.getSimpleName();
	public static final String FILE_EXTENSION = "velvet";

	protected File featureModelFile;

	private static final String[] SYMBOLS = { "!", "&&", "||", "->", "<->", ", ", "choose", "atleast", "atmost" };
	private static final String NEWLINE = System.getProperty("line.separator", "\n");
	private final StringBuilder sb = new StringBuilder();

	public VelvetFeatureModelFormat(VelvetFeatureModelFormat oldFormat) {
		super(oldFormat);
		useLongNames = oldFormat.useLongNames;
	}

	/**
	 * If true an interface will be created. Otherwise it is named CONCEPT
	 */
	private boolean isInterface = false;

	private boolean useLongNames;

	public VelvetFeatureModelFormat() {
		useLongNames = false;
	}

	@Override
	public boolean supportsRead() {
		return true;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String write(IFeatureModel object) {
		if (object instanceof ExtendedFeatureModel) {
			extFeatureModel = (ExtendedFeatureModel) object;
			isInterface = isInterface || extFeatureModel.isInterface();
		}
		final IFeatureStructure root = object.getStructure().getRoot();
		sb.delete(0, sb.length());

		if (isInterface) {
			sb.append("cinterface ");
		} else {
			sb.append("concept ");
		}
		sb.append(root.getFeature().getName());
		if (extFeatureModel != null) {
			usedVariables.clear();
			final LinkedList<ExtendedFeatureModel.UsedModel> inheritedModels = new LinkedList<>();
			final LinkedList<ExtendedFeatureModel.UsedModel> instanceModels = new LinkedList<>();
			final LinkedList<ExtendedFeatureModel.UsedModel> interfaceModels = new LinkedList<>();
			for (final UsedModel usedModel : extFeatureModel.getExternalModels().values()) {
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
				useLongNames = true;
				sb.append(" : ");
				sb.append(inheritedModels.removeFirst().getModelName());
				for (final UsedModel usedModel : inheritedModels) {
					sb.append(", ");
					sb.append(usedModel.getModelName());
				}
			}

			if (!instanceModels.isEmpty()) {
				useLongNames = true;
				sb.append(NEWLINE);
				sb.append("\tinstance ");
				sb.append(instanceModels.removeFirst());
				for (final UsedModel usedModel : instanceModels) {
					sb.append(", ");
					sb.append(usedModel);
				}
			}

			if (!interfaceModels.isEmpty()) {
				useLongNames = true;
				sb.append(NEWLINE);
				sb.append("\tinterface ");
				sb.append(interfaceModels.removeFirst());
				for (final UsedModel usedModel : interfaceModels) {
					sb.append(", ");
					sb.append(usedModel);
				}
			}
		}
		sb.append(" {");
		sb.append(NEWLINE);

		if ((extFeatureModel != null) && !isInterface) {
			for (final IFeatureStructure child : root.getChildren()) {
				writeNewDefined(child, 1);
			}

			for (final IConstraint constraint : object.getConstraints()) {
				if (((ExtendedConstraint) constraint).getType() == ExtendedFeature.TYPE_INTERN) {
					sb.append("\tconstraint ");
					sb.append(constraint.getNode().toString(SYMBOLS));
					sb.append(";");
					sb.append(NEWLINE);
				}
			}
		} else {
			writeFeatureGroup(root, 1);

			for (final IConstraint constraint : object.getConstraints()) {
				sb.append("\tconstraint ");
				sb.append(constraint.getNode().toString(SYMBOLS));
				sb.append(";");
				sb.append(NEWLINE);
			}
		}

		sb.append("}");

		return sb.toString();
	}

	private void writeFeatureGroup(IFeatureStructure root, int depth) {
		if (root.isAnd()) {
			for (final IFeatureStructure feature : root.getChildren()) {
				writeNewDefined(feature, depth + 1);
			}
		} else if (root.isOr()) {
			writeTab(depth + 1);
			sb.append("someOf {");
			sb.append(NEWLINE);
			for (final IFeatureStructure feature : root.getChildren()) {
				writeFeature(feature, depth + 2);
			}
			writeTab(depth + 1);
			sb.append("}");
			sb.append(NEWLINE);
		} else if (root.isAlternative()) {
			writeTab(depth + 1);
			sb.append("oneOf {");
			sb.append(NEWLINE);
			for (final IFeatureStructure f : root.getChildren()) {
				writeFeature(f, depth + 2);
			}
			writeTab(depth + 1);
			sb.append("}");
			sb.append(NEWLINE);
		}
	}

	private void writeFeature(IFeatureStructure feature, int depth) {
		writeTab(depth);
		if (feature.isAbstract()) {
			sb.append("abstract ");
		}
		if (feature.isMandatory() && ((feature.getParent() == null) || feature.getParent().isAnd())) {
			sb.append("mandatory ");
		}
		sb.append("feature ");
		sb.append(feature.getFeature().getName());
		final String description = feature.getFeature().getProperty().getDescription();
		final boolean hasDescription = (description != null) && !description.isEmpty();

		if ((feature.getChildrenCount() == 0) && !hasDescription) {
			sb.append(";");
		} else {
			sb.append(" {");
			sb.append(NEWLINE);
			if (hasDescription) {
				writeTab(depth + 1);
				sb.append("description \"");
				sb.append(description.replace("\"", "\\\""));
				sb.append("\";");
				sb.append(NEWLINE);
			}

			writeFeatureGroup(feature, depth);

			writeTab(depth);
			sb.append("}");
		}
		sb.append(NEWLINE);
	}

	// TODO fix write for inherited feature models
	private void writeNewDefined(IFeatureStructure child2, int depth) {
		final IFeature feature = child2.getFeature();
		if (feature instanceof ExtendedFeature) {
			final ExtendedFeature extFeature = (ExtendedFeature) feature;

			if ((extFeature.getType() == ExtendedFeature.TYPE_INSTANCE) || (extFeature.getType() == ExtendedFeature.TYPE_INTERFACE)) {
				if (usedVariables.add(extFeature.getExternalModelName())) {
					writeTab(depth);
					sb.append(USE);
					sb.append(extFeature.getExternalModelName());
					sb.append(";");
					sb.append(NEWLINE);
				}
			} else if (extFeature.getType() == ExtendedFeature.TYPE_INTERN) {
				writeFeature(child2, 1);
			}
		}
		for (final IFeatureStructure child : child2.getChildren()) {
			writeNewDefined(child, depth);
		}
	}

	private void writeTab(int times) {
		for (int i = 0; i < times; i++) {
			sb.append('\t');
		}
	}

	@Override
	public ProblemList read(IFeatureModel object, CharSequence source) {
		final ProblemList problemList = new ProblemList();
		factory = ExtendedFeatureModelFactory.getInstance();
		extFeatureModel = (ExtendedFeatureModel) object;
		if (extFeatureModel != null) {
			featureModelFile = extFeatureModel.getSourceFile().toFile();
		}

		final ByteArrayInputStream inputstr = new ByteArrayInputStream(source.toString().getBytes(Charset.availableCharsets().get("UTF-8")));
		try {
			parseInputStream(inputstr);
		} catch (final UnsupportedModelException e) {
			problemList.add(new Problem(e, e.lineNumber));
		}
		return problemList;
	}

	private static class ConstraintNode {

		private final Node computedNode;
		private final Tree rawNode;

		public ConstraintNode(Node computedNode, Tree rawNode) {
			this.computedNode = computedNode;
			this.rawNode = rawNode;
		}
	}

	private static final int[] binaryOperators =
		{ VelvetParser.OP_OR, VelvetParser.OP_AND, VelvetParser.OP_XOR, VelvetParser.OP_IMPLIES, VelvetParser.OP_EQUIVALENT };
	private static final String[] paths = { "%s.velvet", "%s.xml", "MPL/%s.velvet", "MPL/%s.xml" };

	private final LinkedList<Tree> atrributeConstraintNodes = new LinkedList<Tree>();
	private final LinkedList<IFeature> parentStack = new LinkedList<IFeature>();
	private final LinkedList<ConstraintNode> constraintNodeList = new LinkedList<ConstraintNode>();
	private final HashSet<String> usedVariables = new HashSet<String>();

	// TODO
	private final boolean velvetImport = false;

	private ModelMarkerHandler<IResource> modelMarkerHandler;
	private ExtendedFeatureModel extFeatureModel;
	private String extFeatureModelName;
	private boolean localSearch = false;

	/**
	 * Reads external model with the right FeatureModelReader.
	 *
	 * @param file file of feature model
	 * @return the feature model or null if error occurred
	 */
	private IFeatureModel readExternalModelFile(File file) {
		return FeatureModelManager.load(file.toPath()).getObject();
	}

	private boolean checkExternalModelFile(Tree curNode) {
		if (localSearch) {
			if (localSearch(curNode.getText()) == null) {
				reportWarning(curNode, format("No model for %s could be found.", curNode.getText()));
				return false;
			}
			return true;
		}
		if (getExternalModelFile(curNode.getText()) == null) {
			reportWarning(curNode, format("No model for %s could be found.", curNode.getText()));
			return false;
		}
		return true;
	}

	private boolean checkInterfaceModelFile(Tree curNode) {
		if (localSearch) {
			if (localSearch(curNode.getText()) == null) {
				reportWarning(curNode, format("No model for %s could be found.", curNode.getText()));
				return false;
			}
			return true;
		}
		if (getInterfaceModelFile(curNode.getText()) == null) {
			reportWarning(curNode, format("No interface for %s could be found.", curNode.getText()));
			return false;
		}
		return true;
	}

	private void copyChildnodes(final ExtendedFeatureModel targetModel, final IFeatureStructure targetParentNode, final IFeatureStructure sourceParentNode,
			final String parentModelName, final String targetParentName, final int type) {
		for (final IFeatureStructure sourceChildStructure : sourceParentNode.getChildren()) {
			final ExtendedFeature feature;
			if (velvetImport) {
				feature = (ExtendedFeature) factory.createFeature(targetModel, sourceChildStructure.getFeature().getName());
			} else {
				final String shortName = sourceChildStructure.getFeature().getName().replace(sourceParentNode.getFeature().getName() + ".", "");
				feature = (ExtendedFeature) factory.createFeature(targetModel, targetParentName + "." + shortName);
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

	private static WeightedTerm createTerm(final int weight, final boolean rightSide, final boolean minus, final Reference reference) {
		boolean positive = weight >= 0;
		if (rightSide ^ minus) {
			positive = !positive;
		}
		return new WeightedTerm(Math.abs(weight), positive, reference);
	}

	private static LinkedList<Tree> getChildren(final Tree root) {
		final LinkedList<Tree> children = new LinkedList<Tree>();

		final int childCount = root.getChildCount();
		for (int i = 0; i < childCount; i++) {
			children.add(root.getChild(i));
		}
		return children;
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

	protected synchronized void parseInputStream(final InputStream inputStream) throws UnsupportedModelException {
		ANTLRInputStream antlrInputStream = null;
		try {
			antlrInputStream = new ANTLRInputStream(inputStream);
		} catch (final IOException e) {
			Logger.logError(e);
			throw new UnsupportedModelException("Error while reading model!", 0);
		}
		final VelvetParser parser = new VelvetParser(new CommonTokenStream(new VelvetLexer(antlrInputStream)));
		Tree root = null;
		try {
			init();
			root = (Tree) parser.velvetModel().getTree();
			if (root == null) {
				throw new UnsupportedModelException("Error while parsing model!", 0);
			}

			checkTree(root);
			parseModel(root);
			parseAttributeConstraints();
		} catch (RecognitionException | VelvetParser.InternalSyntaxException e) {
			RecognitionException re;
			if (e instanceof VelvetParser.InternalSyntaxException) {
				re = ((VelvetParser.InternalSyntaxException) e).getException();
			} else {
				re = (RecognitionException) e;
			}
			Logger.logError(re);
			final String internalMessage = parser.getErrorMessage(re, parser.getTokenNames());
			final String errorMessage = ILLEGAL_SYNTAX_IN_LINE + re.line + ":" + re.charPositionInLine + " (" + internalMessage + ")";
			final UnsupportedModelException unsupportedModelException = new UnsupportedModelException(errorMessage, re.line);
			unsupportedModelException.addSuppressed(re);
			throw unsupportedModelException;
		}
	}

	private ExtendedFeature addFeature(final IFeature parent, final String featureName, final boolean isMandatory, final boolean isAbstract,
			final boolean isHidden) {
		final ExtendedFeature newFeature = (ExtendedFeature) factory.createFeature(extFeatureModel, featureName);
		newFeature.getStructure().setMandatory(isMandatory);
		newFeature.getStructure().setAbstract(isAbstract);
		newFeature.getStructure().setHidden(isHidden);

		final IFeature orgFeature = extFeatureModel.getFeature(featureName);
		if ((orgFeature != null) && (orgFeature instanceof ExtendedFeature)) {
			return (ExtendedFeature) orgFeature;
		} else {
			extFeatureModel.addFeature(newFeature);
			parent.getStructure().addChild(newFeature.getStructure());
			newFeature.setNewDefined(true);
			return newFeature;
		}
	}

	private String checkNode(Node curNode) {
		if (curNode instanceof Literal) {
			final Literal literal = (Literal) curNode;
			final String varString = literal.var.toString();
			if (extFeatureModel.getFeature(varString) == null) {
				return literal.var.toString();
			}
		} else {
			for (final Node child : curNode.getChildren()) {
				final String childRet = checkNode(child);
				if (childRet != null) {
					return childRet;
				}
			}
		}
		return null;
	}

	private IFeatureModel getExternalFeatureModel(Tree curNode) {
		final File modelFile = getExternalModelFile(curNode.getText());
		if (modelFile == null) {
			reportWarning(curNode, format("No model for %s could be found.", curNode.getText()));
			return null;
		}
		return readModel(modelFile, curNode);
	}

	private IFeatureModel getExternalFeatureModel(String modelName, Tree curNode) {
		final File modelFile = getExternalModelFile(modelName);
		if (modelFile == null) {
			return null;
		}
		return readModel(modelFile, curNode);
	}

	private IFeatureModel getInterfaceFeatureModel(String modelName, Tree curNode) {
		final File modelFile = getInterfaceModelFile(modelName);
		if (modelFile == null) {
			return null;
		}
		return readModel(modelFile, curNode);
	}

	private IFeatureModel readModel(File modelFile, Tree curNode) {
		IFeatureModel fm = null;
		if (IS_USED_AS_API) {
			fm = readExternalModelFileAPI(modelFile);
		} else {
			fm = readExternalModelFile(modelFile);
		}
		if (fm == null) {
			reportWarning(curNode, format("External model for %s could not be read.", curNode.getText()));
			return null;
		}
		return fm;
	}

	private IFeatureModel readExternalModelFileAPI(File file) {
		final IFeatureModel fm = new ExtendedFeatureModelFactory().createFeatureModel();
		fm.setSourceFile(file.toPath());
		SimpleFileHandler.load(file.toPath(), fm, FMFormatManager.getInstance());
		return fm;
	}

	/**
	 * Search for the right File to include etc. The following search path is used: <ol> <li>./NAME.velvet</li> <li>./NAME.xml</li> <li>./MPL/NAME.velvet</li>
	 * <li>/NAME_AS_PROJECT/model.xml</li> </ol>
	 *
	 * @param name the name of file or project
	 * @return File object if found else null
	 */
	private File getExternalModelFile(String name) {
		if (!extFeatureModel.getImports().isEmpty() && !IS_USED_AS_API) {
			for (final String path : extFeatureModel.getImports()) {
				final IProject project = getProject();
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

		if (localSearch || IS_USED_AS_API) {
			return localSearch(name);
		}
		File returnFile = null;

		// local search
		IProject project = getProject();
		if (project != null) {
			for (int i = 0; i < paths.length; i++) {
				final IResource res = project.findMember(format(paths[i], name));
				if (res != null) {
					returnFile = res.getLocation().toFile();
					if (returnFile.equals(featureModelFile)) {
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
				if (returnFile.equals(featureModelFile)) {
					return null;
				}
			} else {
				Logger.logWarning(format("Project %s is not accessible.", name));
			}
		}

		if ((returnFile == null) || !returnFile.exists() || !returnFile.canRead()) {
			return null;
		}
		return returnFile;
	}

	private File getInterfaceModelFile(String name) {
		if (localSearch) {
			return localSearch(name);
		}
		File returnFile = null;
		final IProject project = getProject();
		if (project != null) {
			final IResource res = project.findMember(format("Interfaces/%s.velvet", name));
			if (res != null) {
				returnFile = res.getLocation().toFile();
			}
		}
		return returnFile;
	}

	private File localSearch(final String name) {
		if (featureModelFile != null) {
			final File searchDir = new File(featureModelFile.getParentFile(), "MPL");
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

	/**
	 * Returns the eclipse project of the file with the textual representation of the feature model
	 *
	 * @return the project of the file or null if not known
	 */
	private IProject getProject() {
		if ((featureModelFile == null) || IS_USED_AS_API) {
			return null;
		}

		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IPath filePath;
		try {
			filePath = Path.fromOSString(featureModelFile.getCanonicalPath());
			final IFile file = workspace.getRoot().getFileForLocation(filePath);
			if ((null == file) || !file.exists()) {
				return workspace.getRoot().getFile(filePath).getProject();
			}
			return file.getProject();
		} catch (final IOException e) {
			Logger.logError(e);
			return null;
		}
	}

	/**
	 * Initializes all variables.
	 */
	private void init() {
		atrributeConstraintNodes.clear();
		parentStack.clear();
		constraintNodeList.clear();
		usedVariables.clear();

		extFeatureModel.reset();
		// TODO Layout
		// extFeatureModel.getLayout().showHiddenFeatures(true);
		// extFeatureModel.getLayout().verticalLayout(false);
		if (getProject() != null) {
			modelMarkerHandler = new ModelMarkerHandler<IResource>(getProject().getFile(featureModelFile.getName()));
			modelMarkerHandler.deleteAllModelMarkers();
		}

		extFeatureModelName = null;
		extFeatureModel.setInterface(false);

		// TODO MPL: Hack for local search
		localSearch = (featureModelFile != null) && (featureModelFile.getParentFile() != null) && featureModelFile.getParentFile().getName().equals("velvet");
	}

	private void parseAttribute(final Tree root, final IFeature parent) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		final String name = checkTree(nodeList.poll()).getText();
		final Tree valueNode = nodeList.poll();

		switch (valueNode.getType()) {
		case VelvetParser.FLOAT:
			break;
		case VelvetParser.INT:
			extFeatureModel.addAttribute(parent.getName(), name, Integer.parseInt(valueNode.getText()));
			break;
		case VelvetParser.BOOLEAN:
			extFeatureModel.addAttribute(parent.getName(), name, Boolean.parseBoolean(valueNode.getText()));
			break;
		case VelvetParser.STRING:
			final String valueNodeText = valueNode.getText();
			extFeatureModel.addAttribute(parent.getName(), name, valueNodeText.substring(1, valueNodeText.length() - 1));
			break;
		default:
			reportSyntaxError(valueNode);
		}
	}

	private void parseAttributeConstraints() throws UnsupportedModelException, RecognitionException {
		while (!atrributeConstraintNodes.isEmpty()) {
			final LinkedList<Tree> nodeList = getChildren(atrributeConstraintNodes.poll());

			final LinkedList<WeightedTerm> weightedTerms = new LinkedList<WeightedTerm>();
			RelationOperator relationOperator = null;
			boolean minus = false;
			int degree = 0;

			while (!nodeList.isEmpty()) {
				final Tree curNode = nodeList.poll();

				switch (curNode.getType()) {
				case VelvetParser.ID:
				case VelvetParser.IDPath:
					final String attributeName = curNode.getText();

					final Collection<FeatureAttribute<Integer>> attributes = extFeatureModel.getIntegerAttributes().getAttributes(attributeName);

					if (attributes == null) {
						throw new UnsupportedModelException(curNode.getLine() + ":" + curNode.getCharPositionInLine() + NO_SUCH_ATTRIBUTE_DEFINED_,
								curNode.getLine());
					}

					for (final FeatureAttribute<Integer> attr : attributes) {
						weightedTerms.add(createTerm(attr.getValue(), relationOperator != null, minus,
								new Reference(attr.getFeatureName(), ReferenceType.FEATURE, attributeName)));
					}

					break;
				// case VelvetParser.FLOAT:
				// break;
				case VelvetParser.INT:
					final int value = Integer.parseInt(curNode.getText());
					if ((relationOperator == null) ^ minus) {
						degree -= value;
					} else {
						degree += value;
					}
					break;
				case VelvetParser.PLUS:
					minus = false;
					break;
				case VelvetParser.MINUS:
					minus = true;
					break;
				case VelvetParser.ATTR_OP_EQUALS:
					relationOperator = RelationOperator.EQUAL;
					break;
				case VelvetParser.ATTR_OP_NOT_EQUALS:
					relationOperator = RelationOperator.NOT_EQUAL;
					break;
				case VelvetParser.ATTR_OP_GREATER:
					relationOperator = RelationOperator.GREATER;
					break;
				case VelvetParser.ATTR_OP_GREATER_EQ:
					relationOperator = RelationOperator.GREATER_EQUAL;
					break;
				case VelvetParser.ATTR_OP_LESS:
					relationOperator = RelationOperator.LESS;
					break;
				case VelvetParser.ATTR_OP_LESS_EQ:
					relationOperator = RelationOperator.LESS_EQUAL;
					break;
				default:
					reportSyntaxError(curNode);
				}
			}
			final Equation equation = new Equation(weightedTerms, relationOperator, degree);
			extFeatureModel.addAttributeConstraint(equation);
		}
	}

	private void parseConcept(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.ID:
				extFeatureModelName = checkTree(curNode).getText();

				final ExtendedFeature rootFeature = (ExtendedFeature) factory.createFeature(extFeatureModel, extFeatureModelName);
				rootFeature.getStructure().setAbstract(true);
				rootFeature.getStructure().setMandatory(true);

				extFeatureModel.addFeature(rootFeature);
				extFeatureModel.getStructure().setRoot(rootFeature.getStructure());
				parentStack.push(rootFeature);

				break;
			case VelvetParser.BASEEXT:
				useLongNames = true;
				parseInheritance(curNode);
				break;
			case VelvetParser.IMPORTINSTANCE:
				useLongNames = true;
				parseInstanceImport(curNode);
				break;
			case VelvetParser.IMPORTINTERFACE:
				useLongNames = true;
				parseInterfaceImport(curNode);
				break;
			case VelvetParser.DEF:
				parseDefinitions(curNode);
				break;
			default:
				reportSyntaxError(curNode);
			}
		}

		for (final ConstraintNode constraintNode : constraintNodeList) {
			if (!IS_USED_AS_API) {
				final String nameError = checkNode(constraintNode.computedNode);
				if (nameError == null) {
					extFeatureModel.addConstraint(factory.createConstraint(extFeatureModel, constraintNode.computedNode));
				} else {
					reportWarning(constraintNode.rawNode, format("There is no feature with the name %s.", nameError));
				}
			} else {
				extFeatureModel.addConstraint(factory.createConstraint(extFeatureModel, constraintNode.computedNode));
			}
		}
	}

	private void parseConstraint(final Tree root, final IFeature parent) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.ID:
				// name = curNode.getText();
				break;
			case VelvetParser.CONSTR:
				Node newNode = parseConstraint_rec(curNode);
				if (useLongNames) {
					newNode = new Implies(new Literal(parent.getName()), newNode);
				}
				constraintNodeList.add(new ConstraintNode(newNode, curNode));
				break;
			case VelvetParser.ACONSTR:
				atrributeConstraintNodes.add(curNode);
				break;
			default:
				reportSyntaxError(curNode);
			}
		}
	}

	private Node parseConstraint_rec(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);
		final LinkedList<Node> nodes = new LinkedList<Node>();
		final LinkedList<Integer> operators = new LinkedList<Integer>();
		final LinkedList<Integer> unaryOp = new LinkedList<Integer>();
		Node n = null;

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.UNARYOP:
				unaryOp.push(curNode.getChild(0).getType());
				break;
			case VelvetParser.CONSTR:
				n = parseConstraint_rec(curNode);
				break;
			case VelvetParser.OPERAND:
				n = new Literal(curNode.getChild(0).getText());
				break;
			default:
				operators.add(curNode.getType());
			}

			if (n != null) {
				while (!unaryOp.isEmpty()) {
					switch (unaryOp.pop()) {
					case VelvetParser.OP_NOT:
						n = new Not(n);
					}
				}
				nodes.add(n);
				n = null;
			}
		}
		if (!operators.isEmpty()) {
			for (final int operator : binaryOperators) {
				final ListIterator<Node> nodesIt = nodes.listIterator();
				for (final ListIterator<Integer> opIt = operators.listIterator(); opIt.hasNext();) {
					final Node operand1 = nodesIt.next();
					if (opIt.next() == operator) {
						opIt.remove();
						nodesIt.remove();
						final Node operand2 = nodesIt.next();
						switch (operator) {
						case VelvetParser.OP_AND:
							nodesIt.set(new And(operand1, operand2));
							break;
						case VelvetParser.OP_OR:
							nodesIt.set(new Or(operand1, operand2));
							break;
						case VelvetParser.OP_XOR:
							nodesIt.set(new Choose(1, operand1, operand2));
							break;
						case VelvetParser.OP_IMPLIES:
							nodesIt.set(new Implies(operand1, operand2));
							break;
						case VelvetParser.OP_EQUIVALENT:
							nodesIt.set(new Equals(operand1, operand2));
							break;
						}
						nodesIt.previous();
					}
				}
			}
		}
		if (nodes.isEmpty()) {
			return null;
		}

		return nodes.getFirst();
	}

	private void parseDefinitions(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		final IFeature parentFeature = parentStack.pop();
		// parentFeature.getStructure().setAnd();

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			// Feature
			case VelvetParser.FEATURE:
				parseFeature(curNode, parentFeature);
				break;
			// Feature-Group
			case VelvetParser.GROUP:
				parseFeatureGroup(curNode, parentFeature);
				break;
			// Constraint
			case VelvetParser.CONSTRAINT:
				parseConstraint(curNode, parentFeature);
				break;
			// Use
			case VelvetParser.USE:
				parseUse(curNode, parentFeature);
				break;
			// Attribute
			case VelvetParser.ATTR:
				parseAttribute(curNode, parentFeature);
				break;
			case VelvetParser.DESCRIPTION:
				parseDescription(curNode, parentFeature);
				break;
			case VelvetParser.EMPTY:
				break;
			default:
				reportSyntaxError(curNode);
			}
		}

	}

	private void parseDescription(Tree root, IFeature parent) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);
		final Tree valueNode = nodeList.poll();

		switch (valueNode.getType()) {
		case VelvetParser.STRING:
			final String valueNodeText = valueNode.getText();
			parent.getProperty().setDescription(valueNodeText.substring(1, valueNodeText.length() - 1).replace("\\\"", "\""));
			break;
		default:
			reportSyntaxError(valueNode);
		}
	}

	// XXX Quickfix for issue #383, useLongNames should only be active for MPL models
	private void parseFeature(final Tree root, IFeature parent) throws RecognitionException {
		final LinkedList<Tree> childList = getChildren(root);
		final String featureName;
		if (extFeatureModel.isInterface()) {
			featureName = checkTree(childList.poll()).getText();
		} else {
			final String childName = checkTree(childList.poll()).getText();
			if (useLongNames && !childName.startsWith(parent.getName())) {
				featureName = parent.getName() + "." + childName;
			} else {
				featureName = childName;
			}
		}
		boolean isMandatory = false, isAbstract = false, moreDefinitions = false;

		Tree childNode = null;
		while (!childList.isEmpty() && !moreDefinitions) {
			childNode = childList.poll();

			switch (childNode.getType()) {
			case VelvetParser.MANDATORY:
				isMandatory = true;
				break;
			case VelvetParser.ABSTRACT:
				isAbstract = true;
				break;
			case VelvetParser.DEF:
				moreDefinitions = true;
				break;
			default:
				reportSyntaxError(childNode);
			}
		}

		final ExtendedFeature newFeature = addFeature(parent, featureName, isMandatory, isAbstract, false);
		if (moreDefinitions) {
			parentStack.push(newFeature);
			parseDefinitions(childNode);
		}
	}

	private void parseFeatureGroup(final Tree root, final IFeature parent) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();

			switch (curNode.getType()) {
			case VelvetParser.SOMEOF:
				parent.getStructure().setOr();
				break;
			case VelvetParser.ONEOF:
				parent.getStructure().setAlternative();
				break;
			case VelvetParser.FEATURE:
				parseFeature(curNode, parent);
				break;
			default:
				reportSyntaxError(curNode);
			}
		}
	}

	private void parseInheritance(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();
			final String parentModelName = checkTree(curNode).getText();

			final IFeatureModel fm = getExternalFeatureModel(curNode);
			if (fm == null) {
				return;
			}

			if (!extFeatureModel.addInheritance(parentModelName, parentModelName)) {
				reportWarning(curNode, THE_PARENT_MODEL + parentModelName + IS_ALREADY_USED_);
				return;
			}
			addExternalFeatures(fm, parentModelName, extFeatureModel.getStructure().getRoot(), ExtendedFeature.TYPE_INHERITED);
		}
	}

	private void addExternalFeatures(IFeatureModel sourceModel, String sourceModelName, IFeatureStructure targetParentFeature, int type) {
		if (sourceModel instanceof ExtendedFeatureModel) {
			for (final UsedModel usedModel : ((ExtendedFeatureModel) sourceModel).getExternalModels().values()) {
				extFeatureModel.addExternalModel(new UsedModel(usedModel, sourceModelName));
			}
		}

		final UsedModel usedModel = extFeatureModel.getExternalModel(sourceModelName);
		if (usedModel != null) {
			usedModel.setPrefix(targetParentFeature.getFeature().getName() + "." + sourceModelName);
		}

		final IFeatureStructure instanceRoot = sourceModel.getStructure().getRoot();

		String connectorName = "";
		if (type == ExtendedFeature.TYPE_INHERITED) {
			connectorName = targetParentFeature.getFeature().getName();
		} else {
			connectorName = (targetParentFeature.isRoot() && targetParentFeature.getFeature().getName().equals(sourceModelName))
				? targetParentFeature.getFeature().getName() : targetParentFeature.getFeature().getName() + "." + sourceModelName;
		}
		final ExtendedFeature connector = addFeature(targetParentFeature.getFeature(), connectorName, true, true, instanceRoot.isHidden());
		connector.setType(type);
		connector.setExternalModelName(sourceModelName);
		if (instanceRoot.isAlternative()) {
			connector.getStructure().setAlternative();
		} else if (instanceRoot.isOr()) {
			connector.getStructure().setOr();
		}

		copyChildnodes(extFeatureModel, connector.getStructure(), instanceRoot, sourceModelName, connectorName, type);

		for (final IConstraint constraint : sourceModel.getConstraints()) {
			final Node constraintNode = constraint.getNode();
			updateConstraintNode(constraintNode, connectorName, instanceRoot.getFeature().getName(), extFeatureModel);
			final ExtendedConstraint newConstraint = (ExtendedConstraint) factory.createConstraint(extFeatureModel, constraintNode);
			newConstraint.setType(type);
			newConstraint.setContainedFeatures();
			extFeatureModel.addConstraint(newConstraint);
		}
	}

	private void parseInterfaceImport(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree idNode = checkTree(nodeList.poll());
			final String interfaceName = idNode.getText();
			final Tree nameNode = checkTree(nodeList.poll());
			final String varName = nameNode.getText();

			if (checkInterfaceModelFile(idNode)) {
				if (!extFeatureModel.addInterface(interfaceName, varName)) {
					reportWarning(idNode, THE_VARIABLE_NAME + varName + IS_ALREADY_IN_USE_);
				}
			}
		}
	}

	private void parseInstanceImport(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);

		while (!nodeList.isEmpty()) {
			final Tree idNode = checkTree(nodeList.poll());
			final String interfaceName = idNode.getText();
			final Tree nameNode = checkTree(nodeList.poll());
			final String varName = nameNode.getText();

			if (checkExternalModelFile(idNode)) {
				if (!extFeatureModel.addInstance(interfaceName, varName)) {
					reportWarning(idNode, THE_VARIABLE_NAME + varName + IS_ALREADY_IN_USE_);
				}
			}
		}
	}

	private void parseModel(final Tree root) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(root);
		while (!nodeList.isEmpty()) {
			final Tree curNode = nodeList.poll();
			switch (curNode.getType()) {
			case VelvetParser.IMPORT:
				useLongNames = true;
				parseImport(curNode);
				break;
			case VelvetParser.CONCEPT:
				parseConcept(curNode);
				break;
			case VelvetParser.CINTERFACE:
				extFeatureModel.setInterface(true);
				parseConcept(curNode);
				break;
			case VelvetParser.EOF:
				if (curNode.getTokenStartIndex() > -1) {
					break;
				}
			default:
				reportSyntaxError(curNode);
			}
		}
		if (!IS_USED_AS_API) {
			final IFeatureModelFactory mappingModelFactory = FMFactoryManager.getDefaultFactory();
			final IFeatureModel mappingModel = mappingModelFactory.createFeatureModel();
			final IFeatureStructure rootFeature = mappingModelFactory.createFeature(mappingModel, "MPL").getStructure();
			rootFeature.setAnd();
			rootFeature.setAbstract(true);
			rootFeature.setMandatory(true);

			final LinkedList<String> possibleProjects = new LinkedList<String>();
			final IProject[] projects = ResourcesPlugin.getWorkspace().getRoot().getProjects();
			for (int i = 0; i < projects.length; i++) {
				final IProject project = projects[i];
				if (project.isAccessible()) {
					possibleProjects.add(project.getName());
				}
			}

			for (final Entry<String, UsedModel> parameter : extFeatureModel.getExternalModels().entrySet()) {
				if (parameter.getValue().getType() == ExtendedFeature.TYPE_INTERFACE) {
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
			extFeatureModel.setMappingModel(mappingModel);
		}
	}

	private void parseImport(Tree curNode) throws RecognitionException {
		final LinkedList<Tree> nodeList = getChildren(curNode);
		while (!nodeList.isEmpty()) {
			final Tree node = nodeList.poll();
			final String text = node.getText();
			extFeatureModel.addImport(text);
		}
	}

	private void parseUse(Tree root, IFeature parent) throws RecognitionException {
		final LinkedList<Tree> childList = getChildren(root);
		final Tree useNameNode = checkTree(childList.poll());
		final String varName = useNameNode.getText();

		if (!usedVariables.add(varName)) {
			reportWarning(useNameNode, format("The Variable with the name %s was already used in this model.", varName));
			return;
		}

		final UsedModel usedModel = extFeatureModel.getExternalModel(varName);
		if (usedModel == null) {
			reportWarning(useNameNode, format("No variable with the name %s found.", varName));
			return;
		}

		switch (usedModel.getType()) {
		case ExtendedFeature.TYPE_INTERFACE:
			final IFeatureModel interfaceModel = getInterfaceFeatureModel(usedModel.getModelName(), useNameNode);
			if (interfaceModel == null) {
				return;
			}
			addExternalFeatures(interfaceModel, varName, parent.getStructure(), ExtendedFeature.TYPE_INTERFACE);
			break;
		case ExtendedFeature.TYPE_INSTANCE:
			final IFeatureModel instanceModel = getExternalFeatureModel(usedModel.getModelName(), useNameNode);
			if (instanceModel == null) {
				return;
			}
			addExternalFeatures(instanceModel, varName, parent.getStructure(), ExtendedFeature.TYPE_INSTANCE);
			break;
		default:
			reportWarning(useNameNode, format("The variable with the name %s is no interface or instance.", varName));
		}
	}

	private void reportWarning(Tree curNode, String message) {
		if (modelMarkerHandler != null) {
			modelMarkerHandler.createModelMarker(message, org.eclipse.core.resources.IMarker.SEVERITY_WARNING, curNode.getLine());
		}
		Logger.logWarning(message + " (at line " + curNode.getLine() + ((featureModelFile != null) ? IN_FILE + featureModelFile.getName() : "") + ": \""
			+ curNode.getText() + "\")");
	}

	private Tree checkTree(Tree root) throws RecognitionException {
		if (root instanceof CommonErrorNode) {
			throwException(((CommonErrorNode) root).trappedException, root);
		}
		return root;
	}

	private void reportSyntaxError(Tree curNode) throws RecognitionException {
		checkTree(curNode);
		final RecognitionException ex = new RecognitionException();
		ex.line = 1;
		ex.charPositionInLine = 1;
		throwException(ex, curNode);
	}

	private void throwException(RecognitionException e, Tree curNode) throws RecognitionException {
		if (modelMarkerHandler != null) {
			final String text = "";

			if (curNode != null) {
				curNode.getText();
			}
			final String message = ILLEGAL_SYNTAX_IN_LINE + e.line + ":" + e.charPositionInLine + ". " + text;
			modelMarkerHandler.createModelMarker(message, org.eclipse.core.resources.IMarker.SEVERITY_ERROR, e.line);
		}
		throw e;
	}

	@Override
	public String getSuffix() {
		return FILE_EXTENSION;
	}

	@Override
	public VelvetFeatureModelFormat getInstance() {
		return new VelvetFeatureModelFormat(this);
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public String getName() {
		return "Velvet";
	}

}
