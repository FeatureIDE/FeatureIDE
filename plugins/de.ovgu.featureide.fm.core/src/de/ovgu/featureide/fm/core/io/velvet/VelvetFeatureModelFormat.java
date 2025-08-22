/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
 * 				 2025  Malte Grave, VaSiCS, LIT CPS Lab, Johannes Kepler University, Linz
 * 				 2025  Oleksandr Kudriavchenko, VaSiCS, LIT CPS Lab, Johannes Kepler University, Linz
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

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.Tree;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.ModelMarkerHandler;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.MultiConstraint;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel.UsedModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModelFactory;
import de.ovgu.featureide.fm.core.constraint.Equation;
import de.ovgu.featureide.fm.core.constraint.FeatureAttribute;
import de.ovgu.featureide.fm.core.constraint.FeatureAttributeMap;
import de.ovgu.featureide.fm.core.constraint.WeightedTerm;
import de.ovgu.featureide.fm.core.io.AFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;

/**
 * Reads / Writes feature models in the Velvet format.
 *
 * @author Sebastian Krieter
 * @author Matthias Strauss
 * @author Reimar Schroeter
 * @author Malte Grave
 * @author Oleksandr Kudriavchenko
 */
public class VelvetFeatureModelFormat extends AFeatureModelFormat implements IVelvetFeatureModelFormat {

	public static boolean IS_USED_AS_API = false;
	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + VelvetFeatureModelFormat.class.getSimpleName();
	public static final String FILE_EXTENSION = "velvet";
	File featureModelFile;
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

	<T> void collectAttributes(Map<String, String> attributesMap, FeatureAttributeMap<T> attributes, String type) {
		for (final String key : attributes.getKeys()) {
			for (final FeatureAttribute<T> attribute : attributes.getAttributes(key)) {

				attributesMap.put(String.format("%s %s = %s;", type, attribute.getAttributeName(), attribute.getValue()), attribute.getFeatureName());
			}
		}
	}

	@Override
	public String write(IFeatureModel object) {
		final int depth = 0;

		if (object instanceof MultiFeatureModel) {
			extFeatureModel = (MultiFeatureModel) object;
			isInterface = isInterface || extFeatureModel.isInterface();
		}
		final Map<String, String> attributes = new HashMap<>();
		final FeatureAttributeMap<Integer> intAttrs = extFeatureModel.getIntegerAttributes();
		// final FeatureAttributeMap<Integer> floatAttrs = extFeatureModel.getIntegerAttributes();
		final FeatureAttributeMap<Boolean> boolAttrs = extFeatureModel.getBooleanAttributes();
		final FeatureAttributeMap<String> strAttrs = extFeatureModel.getStringAttributes();
		List<Equation> attributeConstraints = null;
		collectAttributes(attributes, intAttrs, "int");
		collectAttributes(attributes, boolAttrs, "bool");
		collectAttributes(attributes, strAttrs, "string");

		final List<IConstraint> constraints = new ArrayList<>(extFeatureModel.getConstraints());

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
			final LinkedList<MultiFeatureModel.UsedModel> inheritedModels = new LinkedList<>();
			final LinkedList<MultiFeatureModel.UsedModel> instanceModels = new LinkedList<>();
			final LinkedList<MultiFeatureModel.UsedModel> interfaceModels = new LinkedList<>();
			for (final UsedModel usedModel : extFeatureModel.getExternalModels().values()) {
				switch (usedModel.getType()) {
				case MultiFeature.TYPE_INHERITED:
					inheritedModels.add(usedModel);
					break;
				case MultiFeature.TYPE_INSTANCE:
					instanceModels.add(usedModel);
					break;
				case MultiFeature.TYPE_INTERFACE:
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

			attributeConstraints = extFeatureModel.getAttributConstraints();
			for (final IFeatureStructure child : root.getChildren()) {
				writeNewDefined(child, 1, constraints, attributes, attributeConstraints);
			}

			for (final IConstraint constraint : constraints) {
				if (((MultiConstraint) constraint).getType() == MultiFeature.TYPE_INTERN) {
					writeConstraint(constraint, depth);
				}
			}
		} else {
			writeFeatureGroup(root, 1, constraints, attributes, attributeConstraints);

			for (final IConstraint constraint : object.getConstraints()) {
				writeConstraint(constraint, depth);
			}
		}

		sb.append("}");
		return sb.toString();
	}

	private void writeFeatureGroup(IFeatureStructure root, int depth, List<IConstraint> constraints, Map<String, String> attributes,
			List<Equation> attributeConstraints) {
		if (root.isAnd()) {
			for (final IFeatureStructure feature : root.getChildren()) {
				writeNewDefined(feature, depth + 1, constraints, attributes, attributeConstraints);
			}
		} else if (root.isOr()) {
			writeTab(depth + 1);
			sb.append("someOf {");
			sb.append(NEWLINE);
			for (final IFeatureStructure feature : root.getChildren()) {
				writeFeature(feature, depth + 2, constraints, attributes, attributeConstraints);
			}
			writeTab(depth + 1);
			sb.append("}");

			sb.append(NEWLINE);
		} else if (root.isAlternative()) {
			writeTab(depth + 1);
			sb.append("oneOf {");
			sb.append(NEWLINE);
			for (final IFeatureStructure f : root.getChildren()) {
				writeFeature(f, depth + 2, constraints, attributes, attributeConstraints);
			}
			writeTab(depth + 1);
			sb.append("}");
			sb.append(NEWLINE);
		}
	}

	private void writeFeature(IFeatureStructure feature, int depth, List<IConstraint> constraints, Map<String, String> attributes,
			List<Equation> attributeConstraints) {
		final String featureName = feature.getFeature().getName().toString();
		if (!usedFeatures.add(featureName)) {
			return;
		}
		writeTab(depth);
		if (feature.isAbstract()) {
			sb.append("abstract ");
		}
		if (feature.isMandatory() && ((feature.getParent() == null) || feature.getParent().isAnd())) {
			sb.append("mandatory ");
		}
		sb.append("feature ");
		sb.append(featureName);

		final String description = feature.getFeature().getProperty().getDescription();

		final List<IConstraint> childConstraints = new ArrayList<>();
		final List<Equation> childAttributeConstraints = new ArrayList<>();

		final Iterator<IConstraint> iteratorC = constraints.iterator();
		while (iteratorC.hasNext()) {
			final IConstraint constraint = iteratorC.next();
			final Node constraintNode = constraint.getNode();
			final Node[] children = ((Implies) constraintNode).getChildren();
			final Node parentFeature = children[0];
			if ((parentFeature.toString().equals(featureName))) {
				childConstraints.add(constraint);
				iteratorC.remove();
			}
		}

		final Iterator<Equation> iteratorAC = attributeConstraints.iterator();
		while (iteratorAC.hasNext()) {
			String parentFeature = null;
			final Equation attributeConstraint = iteratorAC.next();

			for (final WeightedTerm term : attributeConstraint.getWeightedTerms()) {
				/*
				 * go through all terms in equation if there is one, that has a parent which is not present in attributes, we see, that it is equations parent
				 */
				if (!attributes.containsValue(term.getReference().toString())) {
					parentFeature = term.getReference().toString();
					break;
				}
			}

			if (featureName.equals(parentFeature)) {
				childAttributeConstraints.add(attributeConstraint);
				iteratorAC.remove();
			}

		}

		final boolean hasDescription = (description != null) && !description.isEmpty();
		final boolean hasConstraints = (childConstraints != null) && !childConstraints.isEmpty();
		final boolean hasAttributeConstraints = (childAttributeConstraints != null) && !childAttributeConstraints.isEmpty();
		final boolean hasAttributes = attributes.containsValue(featureName);

		if ((feature.getChildrenCount() == 0) && !hasDescription && !hasConstraints && !hasAttributes && !hasAttributeConstraints) {
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
			if (hasAttributes) {
				for (final Entry<String, String> attr : attributes.entrySet()) {
					if (attr.getValue().equals(featureName)) {
						writeTab(depth + 1);
						sb.append(attr.getKey());
						sb.append(NEWLINE);
					}
				}
			}
			if (hasAttributeConstraints) {
				for (final Equation attributeConstraint : childAttributeConstraints) {

					writeAttributeConstraint(attributes, attributeConstraint, featureName, depth);
				}
			}
			if (hasConstraints) {
				for (final IConstraint constraint : childConstraints) {

					writeConstraint(constraint, depth);

				}

			}
			writeFeatureGroup(feature, depth, constraints, attributes, attributeConstraints);
			writeTab(depth);
			sb.append("}");
		}
		sb.append(NEWLINE);
	} // TODO fix write for inherited feature models private void

	private void writeConstraint(IConstraint constraint, int depth) {
		writeTab(depth + 1);
		sb.append("constraint ");
		final Node constraintNode = ((Implies) constraint.getNode()).getChildren()[1];

		final Node[] children = ((Equals) constraintNode).getChildren();
		final Node name = children[0];
		final Node value = children[1];
		sb.append(name.toString(SYMBOLS));
		sb.append(" = ");
		sb.append(value.toString(SYMBOLS));
		sb.append(";");
		sb.append(NEWLINE);
	}

	private void writeAttributeConstraint(Map<String, String> attributes, Equation attributeConstraint, String featureName, int depth) {
		writeTab(depth + 1);
		sb.append("constraint ");
		sb.append("ID = ");
		final List<WeightedTerm> sortedTerms = attributeConstraint.getWeightedTerms();
		sortedTerms.sort(Comparator.comparing(WeightedTerm::isPositive).reversed());
		boolean first = true;
		for (final WeightedTerm term : sortedTerms) {
			if (!term.isPositive()) {
				sb.append(" - ");
			} else if (!first) {
				sb.append(" + ");
			}

			final String name = term.getReference().getAttributeName();
			if (!name.equals("attributeName")) {
				sb.append(name);

			} else {
				sb.append(term.getWeight());
			}
			first = false;

		}
		sb.append(" ");
		sb.append(attributeConstraint.getOperator());
		sb.append(" 0;");
		sb.append(NEWLINE);

	}

	private void writeNewDefined(IFeatureStructure child2, int depth, List<IConstraint> constraints, Map<String, String> attributes,
			List<Equation> attributeConstraints) {
		final IFeature feature = child2.getFeature();
		if (feature instanceof MultiFeature) {
			final MultiFeature extFeature = (MultiFeature) feature;
			if (((extFeature.getType() == MultiFeature.TYPE_INSTANCE) || (extFeature.getType() == MultiFeature.TYPE_INTERFACE))) {
				if ((usedVariables.add(extFeature.getExternalModelName()))) {
					writeTab(depth);
					sb.append("use ");
					sb.append(extFeature.getExternalModelName());
					sb.append(";");
					sb.append(NEWLINE);

				}
				writeFeature(child2, depth, constraints, attributes, attributeConstraints);

			} else if ((extFeature.getType() == MultiFeature.TYPE_INTERN)) {

				writeFeature(child2, depth, constraints, attributes, attributeConstraints);
			}
		}
		for (final IFeatureStructure child : child2.getChildren()) {
			writeNewDefined(child, depth, constraints, attributes, attributeConstraints);
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
		factory = MultiFeatureModelFactory.getInstance();
		extFeatureModel = (MultiFeatureModel) object;
		if (extFeatureModel != null) {
			featureModelFile = extFeatureModel.getSourceFile().toFile(); // .toAbsolutePath();
		}
		final ByteArrayInputStream inputstr = new ByteArrayInputStream(source.toString().getBytes(Charset.availableCharsets().get("UTF-8")));
		try {
			parseInputStream(inputstr);
		} catch (final UnsupportedModelException e) {
			problemList.add(new Problem(e, e.lineNumber));
		}
		return problemList;
	}

	protected synchronized void parseInputStream(final InputStream inputStream) throws UnsupportedModelException {
		CharStream charStream = null;
		try {
			charStream = CharStreams.fromStream(inputStream);
		} catch (final IOException e) {
			Logger.logError(e);
			throw new UnsupportedModelException("Error while reading model!", 0);
		}
		init();

		final VelvetLexer lexer = new VelvetLexer(charStream);
		final CommonTokenStream tokens = new CommonTokenStream(lexer);
		final VelvetParser parser = new VelvetParser(tokens);
		final VelvetVisitorImpl visitor = new VelvetVisitorImpl(this);
		try {

			final ParseTree tree = parser.velvetModel();
			visitor.visit(tree);

		} catch (RecognitionException | VelvetParser.InternalSyntaxException e) {
			RecognitionException re;
			if (e instanceof VelvetParser.InternalSyntaxException) {
				re = ((VelvetParser.InternalSyntaxException) e).getException();
			} else {
				re = (RecognitionException) e;
			}

			Logger.logError(re);
			/*
			 * TODO newer parser doesn't have those methods. final String internalMessage = parser.getErrorMessage(re, parser.getTokenNames()); final String
			 * errorMessage = "ILLEGAL_SYNTAX_IN_LINE" + re.line + ":" + re.charPositionInLine + " (" + internalMessage + ")"; final UnsupportedModelException
			 * unsupportedModelException = new UnsupportedModelException(errorMessage, re.line); unsupportedModelException.addSuppressed(re); throw
			 * unsupportedModelException;
			 */

		}
	}

	private static final int[] binaryOperators =
		{ VelvetParser.OP_OR, VelvetParser.OP_AND, VelvetParser.OP_XOR, VelvetParser.OP_IMPLIES, VelvetParser.OP_EQUIVALENT };
	private static final String[] paths = { "%s.velvet", "%s.xml", "MPL/%s.velvet", "MPL/%s.xml" };
	private final LinkedList<Tree> atrributeConstraintNodes = new LinkedList<>();
	private final LinkedList<IFeature> parentStack = new LinkedList<>();
	private final HashSet<String> usedVariables = new HashSet<>(); // TODO private final
	private final HashSet<String> usedFeatures = new HashSet<>();
	boolean velvetImport = false;
	private ModelMarkerHandler<IResource> modelMarkerHandler;
	MultiFeatureModel extFeatureModel;
	String extFeatureModelName;
	private boolean localSearch = false;

	/**
	 * Returns the eclipse project of the file with the textual representation of the feature model
	 *
	 * @return the project of the file or null if not known
	 * @throws IOException
	 */

	@Override
	public IProject getProject() {
		if ((featureModelFile == null) || IS_USED_AS_API) {
			return null;
		}
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		IPath filePath = null;
		try {
			filePath = new Path(featureModelFile.getCanonicalPath());
		} catch (final IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		final IFile file = workspace.getRoot().getFileForLocation(filePath);
		if ((null == file) || !file.exists()) {
			return workspace.getRoot().getFile(filePath).getProject();
		}
		return file.getProject();
	}

	/**
	 * Initializes all variables.
	 */
	private void init() {
		usedFeatures.clear();
		usedVariables.clear();
		extFeatureModel.reset(); // TODO Layout
		if (getProject() != null) {
			modelMarkerHandler = new ModelMarkerHandler<IResource>(getProject().getFile(featureModelFile.getName()));
			modelMarkerHandler.deleteAllModelMarkers();
		}
		extFeatureModelName = null;
		extFeatureModel.setInterface(false); // TODO MPL: Hack for local search
		localSearch = (featureModelFile != null) && (featureModelFile.getParent() != null) && featureModelFile.getName().equals("velvet");
	}

	private void reportWarning(Tree curNode, String message) {
		/*
		 * if (modelMarkerHandler != null) { modelMarkerHandler.createModelMarker(message, org.eclipse.core.resources.IMarker.SEVERITY_WARNING,
		 * curNode.getLine()); } Logger.logWarning(message + " (at line " + curNode.getLine() + ((featureModelFile != null) ? IN_FILE +
		 * featureModelFile.getName() : "") + ": \"" + curNode.getText() + "\")");
		 */
	}

	private void reportSyntaxError(Tree curNode) throws RecognitionException {
		/*
		 * final RecognitionException ex = new RecognitionException(null, null, null); ex.line = 1; ex.charPositionInLine = 1; throwException(ex, curNode);
		 */
	}

	private void throwException(RecognitionException e, Tree curNode) throws RecognitionException {
		/*
		 * if (modelMarkerHandler != null) { final String text = ""; if (curNode != null) { curNode.getText(); } final String message = ILLEGAL_SYNTAX_IN_LINE +
		 * e.line + ":" + e.charPositionInLine + ". " + text; modelMarkerHandler.createModelMarker(message, org.eclipse.core.resources.IMarker.SEVERITY_ERROR,
		 * e.line); } throw e;
		 */
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

	@Override
	public boolean initExtension() {
		if (super.initExtension()) {
			FMFactoryManager.getInstance().getDefaultFactoryWorkspace().assignID(VelvetFeatureModelFormat.ID, MultiFeatureModelFactory.ID);
			return true;
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.velvet.IVelvetFeatureModelFormat#getExtFeatureModelName()
	 */
	@Override
	public String getExtFeatureModelName() {
		return extFeatureModelName;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.velvet.IVelvetFeatureModelFormat#getExtFeatureModel()
	 */
	@Override
	public MultiFeatureModel getExtFeatureModel() {
		return extFeatureModel;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.velvet.IVelvetFeatureModelFormat#setExtFeatureModelName(java.lang.String)
	 */
	@Override
	public void setExtFeatureModelName(String name) {
		extFeatureModelName = name;

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.velvet.IVelvetFeatureModelFormat#getFeatureModelFile()
	 */
	@Override
	public File getFeatureModelFile() {

		return featureModelFile;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.velvet.IVelvetFeatureModelFormat#isVelvetImport()
	 */
	@Override
	public boolean isVelvetImport() {
		return velvetImport;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.velvet.IVelvetFeatureModelFormat#getLocalSearch()
	 */
	@Override
	public boolean getLocalSearch() {
		return localSearch;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.velvet.IVelvetFeatureModelFormat#getIsUsedAsAPI()
	 */
	@Override
	public boolean getIsUsedAsAPI() {
		// TODO Auto-generated method stub
		return IS_USED_AS_API;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.io.velvet.IVelvetFeatureModelFormat#getPaths()
	 */
	@Override
	public String[] getPaths() {
		return paths;
	}

}
