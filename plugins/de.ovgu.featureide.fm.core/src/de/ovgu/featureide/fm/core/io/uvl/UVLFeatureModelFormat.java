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
package de.ovgu.featureide.fm.core.io.uvl;

import java.io.File;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.BiFunction;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.eclipse.core.resources.IProject;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.MultiConstraint;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.AFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.Problem.Severity;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.vill.config.Configuration;
import de.vill.exception.ParseError;
import de.vill.main.UVLModelFactory;
import de.vill.model.Attribute;
import de.vill.model.Feature;
import de.vill.model.FeatureModel;
import de.vill.model.Group;
import de.vill.model.Group.GroupType;
import de.vill.model.Import;
import de.vill.model.constraint.AndConstraint;
import de.vill.model.constraint.Constraint;
import de.vill.model.constraint.EquivalenceConstraint;
import de.vill.model.constraint.ImplicationConstraint;
import de.vill.model.constraint.LiteralConstraint;
import de.vill.model.constraint.NotConstraint;
import de.vill.model.constraint.OrConstraint;
import de.vill.model.constraint.ParenthesisConstraint;

/**
 * Reads / writes feature models in the UVL format.
 *
 * @author Dominik Engelhardt
 * @author Johannes Herschel
 */
public class UVLFeatureModelFormat extends AFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + UVLFeatureModelFormat.class.getSimpleName();
	public static final String FILE_EXTENSION = "uvl";

	private static final String NS_ATTRIBUTE_NAME = "namespace";
	private static final String NS_ATTRIBUTE_FEATURE = "_synthetic_ns_feature";

	protected static final String EXTENDED_ATTRIBUTE_NAME = "extended__";
	private static final String MULTI_ROOT_PREFIX = "Abstract_";

	// Patterns for import validation. The same as in the BNF of the UVL parser.
	private static final Pattern ID_PATTERN = Pattern.compile("(?!true|false)[a-zA-Z][a-zA-Z_0-9]*");
	private static final Pattern STRICT_ID_RESTRICTIVE_PATTERN =
		Pattern.compile("(?!alternative|or|features|constraints|true|false|as|refer)[a-zA-Z][a-zA-Z_0-9]*");

	private FeatureModel rootModel;
	protected ProblemList pl;
	private IFeatureModel fm;
	protected MultiFeatureModelFactory factory;

	@Override
	public String getName() {
		return "UVL";
	}

	@Override
	public String getSuffix() {
		return FILE_EXTENSION;
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public APersistentFormat<IFeatureModel> getInstance() {
		return new UVLFeatureModelFormat();
	}

	@Override
	public ProblemList read(IFeatureModel fm, CharSequence source) {
		if (fm.getSourceFile() != null) {
			return read(fm, source, fm.getSourceFile().toAbsolutePath());
		}
		System.err.println("No path set for model. Can't load imported models.");
		return read(fm, source, new File("./.").toPath());
	}

	@Override
	public ProblemList read(IFeatureModel fm, CharSequence source, Path path) {
		fm.setSourceFile(path);
		this.fm = fm;
		pl = new ProblemList();
		final UVLModelFactory uvlModelFactory = new UVLModelFactory();
		try {
			rootModel = uvlModelFactory.parse(source.toString(), path.getParent().toString());
			constructFeatureModel((MultiFeatureModel) fm);
		} catch (final ParseError e) {
			pl.add(toProblem(e));
		}
		return pl;
	}

	private void constructFeatureModel(MultiFeatureModel fm) {
		factory = (MultiFeatureModelFactory) FMFactoryManager.getInstance().getFactory(fm);
		fm.reset();
		final IFeature rootFeature;
		final Feature uvlRootFeature = rootModel.getRootFeature();
		rootFeature = parseFeature(fm, uvlRootFeature, null);
		fm.getStructure().setRoot(rootFeature.getStructure());
		parseConstraints(fm, rootModel.getOwnConstraints());
	}

	private IFeature parseFeature(MultiFeatureModel fm, Feature uvlFeature, IFeature parentFeature) {
		final MultiFeature feature = factory.createFeature(fm, uvlFeature.getFeatureName());
		fm.addFeature(feature);

		if (parentFeature != null) {
			parentFeature.getStructure().addChild(feature.getStructure());
		}
		if (uvlFeature.getAttributes().containsKey("abstract")) {
			feature.getStructure().setAbstract(true);
		}

		for (final Group group : uvlFeature.getChildren()) {
			parseGroup(fm, group, feature);
		}

		parseAttributes(fm, feature, uvlFeature);
		// todo parse attributes
		return feature;
	}

	private void parseGroup(MultiFeatureModel fm, Group uvlGroup, IFeature parentFeature) {
		final List<IFeature> children = new LinkedList();
		for (final Feature feature : uvlGroup.getFeatures()) {
			children.add(parseFeature(fm, feature, parentFeature));
		}

		if (uvlGroup.GROUPTYPE.equals(GroupType.GROUP_CARDINALITY)) {
			if ((uvlGroup.getLowerBound().equals("1")) && (uvlGroup.getUpperBound().equals("*"))) {
				parentFeature.getStructure().setOr();
			} else if ((uvlGroup.getLowerBound().equals("1")) && (uvlGroup.getUpperBound().equals("1"))) {
				parentFeature.getStructure().setAlternative();
			} else if ((uvlGroup.getLowerBound().equals("0")) && (uvlGroup.getUpperBound().equals("*"))) {
				// optional is true if nothing else is set
			} else if ((uvlGroup.getLowerBound().equals(uvlGroup.getUpperBound())) && (uvlGroup.getUpperBound().equals(uvlGroup.getFeatures().size()))) {
				children.forEach(f -> f.getStructure().setMandatory(true));
			} else {
				pl.add(new Problem(String.format("Failed to convert cardinality [%d..%d] to known group type at feature %s.", uvlGroup.getLowerBound(),
						uvlGroup.getUpperBound(), parentFeature.getName()), 0, Severity.WARNING));
			}
		}

		switch (uvlGroup.GROUPTYPE) {
		case OR:
			parentFeature.getStructure().setOr();
			break;
		case ALTERNATIVE:
			parentFeature.getStructure().setAlternative();
			break;
		case OPTIONAL:
			break;
		case MANDATORY:
			children.forEach(f -> f.getStructure().setMandatory(true));
			break;
		}
	}

	private boolean isAbstract(Feature f) {
		return Objects.equals(true, f.getAttributes().get("abstract"));
	}

	private void parseAttributes(MultiFeatureModel fm, MultiFeature feature, Feature uvlFeature) {
		uvlFeature.getAttributes().entrySet().stream().forEachOrdered(e -> parseAttribute(fm, feature, e.getKey(), e.getValue()));
	}

	protected void parseAttribute(MultiFeatureModel fm, MultiFeature feature, String attributeKey, Attribute attributeValue) {
		if (attributeValue.getValue() instanceof Constraint) {
			parseConstraint(fm, (Constraint) attributeValue.getValue());
		}
		// TODO list with constraints?
	}

	private void parseConstraints(MultiFeatureModel fm, List<Constraint> constraints) {
		for (final Constraint constraint : constraints) {
			parseConstraint(fm, constraint);
		}
	}

	private void parseConstraint(MultiFeatureModel fm, Constraint c) {
		parseConstraint(fm, c, false);
	}

	private void parseOwnConstraint(MultiFeatureModel fm, Constraint c) {
		parseConstraint(fm, c, true);
	}

	private void parseConstraint(MultiFeatureModel fm, Constraint c, boolean own) {
		try {
			final Node constraint = parseConstraint(c);
			if (constraint != null) {
				final MultiConstraint newConstraint = factory.createConstraint(fm, constraint);
				if (own) {
					fm.addOwnConstraint(newConstraint);
				} else {
					newConstraint.setType(MultiFeature.TYPE_INTERFACE);
					fm.addConstraint(newConstraint);
				}
			}
		} catch (final RuntimeException e) {
			// Contained invalid reference. Already added to problem list
		}
	}

	private Node parseConstraint(Constraint constraint) {
		if (constraint instanceof AndConstraint) {
			return new org.prop4j.And(parseConstraint(((AndConstraint) constraint).getLeft()), parseConstraint(((AndConstraint) constraint).getRight()));
		} else if (constraint instanceof EquivalenceConstraint) {
			return new org.prop4j.Equals(parseConstraint(((EquivalenceConstraint) constraint).getLeft()),
					parseConstraint(((EquivalenceConstraint) constraint).getRight()));
		} else if (constraint instanceof ImplicationConstraint) {
			return new org.prop4j.Implies(parseConstraint(((ImplicationConstraint) constraint).getLeft()),
					parseConstraint(((ImplicationConstraint) constraint).getRight()));
		} else if (constraint instanceof NotConstraint) {
			return new org.prop4j.Not(parseConstraint(((NotConstraint) constraint).getContent()));
		} else if (constraint instanceof OrConstraint) {
			return new org.prop4j.Or(parseConstraint(((OrConstraint) constraint).getLeft()), parseConstraint(((OrConstraint) constraint).getRight()));
		} else if (constraint instanceof ParenthesisConstraint) {
			return parseConstraint(((ParenthesisConstraint) constraint).getContent());
		} else if (constraint instanceof LiteralConstraint) {
			return new org.prop4j.Literal(((LiteralConstraint) constraint).getLiteral());
		} else {
			return null;
		}
	}

	private void checkReferenceValid(String name) {
		final IFeature f = fm.getFeature(name);
		if ((f == null) || f.getProperty().isImplicit()) {
			pl.add(new Problem("Invalid reference: Feature " + name + " doesn't exist", 0, Severity.ERROR));
			throw new RuntimeException("Invalid reference");
		}
	}

	private void parseImport(MultiFeatureModel fm, Import i) {
		final IProject project = EclipseFileSystem.getResource(fm.getSourceFile()).getProject();
		// Local path of imported model (as given in importing model)
		final String modelPath = i.getNamespace().replace(".", "/") + "." + FILE_EXTENSION;
		// Resolved path (import relative to project root)
		Path path = project.getFile(modelPath).getLocation().toFile().toPath();
		if (!Files.exists(path)) {
			// Import relative to importing model
			path = fm.getSourceFile().resolveSibling(modelPath);
		}
		fm.addInstance(i.getNamespace(), i.getAlias(), path);
	}

	/**
	 * @param error a {@link ParseError}
	 * @return a {@link Problem}
	 */
	private Problem toProblem(ParseError error) {
		return new Problem(error);
	}

	@Override
	public String write(IFeatureModel fm) {
		Configuration.setTabulatorSymbol("\t");
		return featureIDEModelToUVLFeatureModel(fm).toString();
	}

	private FeatureModel featureIDEModelToUVLFeatureModel(IFeatureModel fm) {
		final FeatureModel uvlModel = new FeatureModel();
		uvlModel.setNamespace(fm.getStructure().getRoot().getFeature().getName());
		final Feature rootFeature = featureIDEFeatureToUVLFeature(fm.getStructure().getRoot().getFeature());
		uvlModel.setRootFeature(rootFeature);
		uvlModel.getOwnConstraints().addAll(featureIDEConstraintsToUVLConstraints(fm));
		return uvlModel;
	}

	private Feature featureIDEFeatureToUVLFeature(IFeature feature) {
		final Feature uvlFeature = new Feature(feature.getName());
		uvlFeature.getAttributes().putAll(featureIDEAttributesToUVLAttributes(feature));

		if (feature.getStructure().isAlternative()) {
			final List<IFeature> alternativeChildren = feature.getStructure().getChildren().stream().map(x -> x.getFeature()).collect(Collectors.toList());
			final Group group = new Group(GroupType.ALTERNATIVE);
			for (final IFeature childFeature : alternativeChildren) {
				group.getFeatures().add(featureIDEFeatureToUVLFeature(childFeature));
			}
			uvlFeature.getChildren().add(group);
		} else if (feature.getStructure().isOr()) {
			final List<IFeature> orChildren = feature.getStructure().getChildren().stream().map(x -> x.getFeature()).collect(Collectors.toList());
			final Group group = new Group(GroupType.OR);
			for (final IFeature childFeature : orChildren) {
				group.getFeatures().add(featureIDEFeatureToUVLFeature(childFeature));
			}
			uvlFeature.getChildren().add(group);
		} else {
			final List<IFeature> mandatoryChildren =
				feature.getStructure().getChildren().stream().filter(x -> x.isMandatory()).map(x -> x.getFeature()).collect(Collectors.toList());
			if (mandatoryChildren.size() > 0) {
				final Group group = new Group(GroupType.MANDATORY);
				for (final IFeature childFeature : mandatoryChildren) {
					group.getFeatures().add(featureIDEFeatureToUVLFeature(childFeature));
				}
				uvlFeature.getChildren().add(group);
			}

			final List<IFeature> optionalChildren =
				feature.getStructure().getChildren().stream().filter(x -> !x.isMandatory()).map(x -> x.getFeature()).collect(Collectors.toList());
			if (optionalChildren.size() > 0) {
				final Group group = new Group(GroupType.OPTIONAL);
				for (final IFeature childFeature : optionalChildren) {
					group.getFeatures().add(featureIDEFeatureToUVLFeature(childFeature));
				}
				uvlFeature.getChildren().add(group);
			}
		}
		return uvlFeature;

	}

	private Map<String, Attribute> featureIDEAttributesToUVLAttributes(IFeature feature) {
		final Map<String, Attribute> attribtues = new HashMap<>();
		if (feature.getStructure().isAbstract()) {
			attribtues.put("abstract", new Attribute("abstract", true));
		}
		return attribtues;
	}

	private List<Constraint> featureIDEConstraintsToUVLConstraints(IFeatureModel fm) {
		final List<Constraint> result = new LinkedList<>();
		for (final IConstraint constraint : fm.getConstraints()) {
			result.add(featureIDEConstraintToUVLConstraint(constraint.getNode()));
		}
		return result;
	}

	private Constraint featureIDEConstraintToUVLConstraint(Node n) {
		System.out.println(n.toString());
		if (n instanceof Literal) {
			return new LiteralConstraint(((Literal) n).var.toString());
		} else if (n instanceof org.prop4j.Not) {
			return new NotConstraint(featureIDEConstraintToUVLConstraint(n.getChildren()[0]));
		} else if (n instanceof org.prop4j.And) {
			return printMultiArity(AndConstraint::new, n.getChildren());
		} else if (n instanceof org.prop4j.Or) {
			return printMultiArity(OrConstraint::new, n.getChildren());
		} else if (n instanceof Implies) {
			return new ImplicationConstraint(featureIDEConstraintToUVLConstraint(n.getChildren()[0]), featureIDEConstraintToUVLConstraint(n.getChildren()[1]));
		} else if (n instanceof Equals) {
			return new EquivalenceConstraint(featureIDEConstraintToUVLConstraint(n.getChildren()[0]), featureIDEConstraintToUVLConstraint(n.getChildren()[1]));
		}
		return null;
	}

	private Constraint printMultiArity(BiFunction<Constraint, Constraint, Constraint> constructor, Node[] args) {
		switch (args.length) {
		case 0:
			return null;
		case 1:
			return featureIDEConstraintToUVLConstraint(args[0]);
		case 2:
			return constructor.apply(featureIDEConstraintToUVLConstraint(args[0]), featureIDEConstraintToUVLConstraint(args[1]));
		default:
			return constructor.apply(featureIDEConstraintToUVLConstraint(args[0]), printMultiArity(constructor, Arrays.copyOfRange(args, 1, args.length)));
		}
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
	public boolean supportsContent(CharSequence content) {
		return !content.toString().contains(EXTENDED_ATTRIBUTE_NAME);
	}

	@Override
	public boolean supportsContent(LazyReader reader) {
		return supportsContent((CharSequence) reader);
	}

	@Override
	public boolean isValidFeatureName(String featureName) {
		return featureName.matches("[^\\\"\\.\\n\\r]*");
	}

	@Override
	public boolean isValidImportName(String name) {
		final String[] splitName = name.split("\\.", -1);
		for (int i = 0; i < (splitName.length - 1); i++) {
			if (!ID_PATTERN.matcher(splitName[i]).matches()) {
				return false;
			}
		}
		return STRICT_ID_RESTRICTIVE_PATTERN.matcher(splitName[splitName.length - 1]).matches();
	}

	@Override
	public boolean isValidImportAlias(String alias) {
		return alias.isEmpty() || ID_PATTERN.matcher(alias).matches();
	}

	@Override
	public String getErrorMessage() {
		return "The characters  \" and . are not allowed and the feature name has to be non-empty.";
	}

	@Override
	public boolean initExtension() {
		FMFactoryManager.getInstance().getDefaultFactoryWorkspace().assignID(getId(), MultiFeatureModelFactory.ID);
		return super.initExtension();
	}

}
