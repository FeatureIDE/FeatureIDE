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
package de.ovgu.featureide.fm.core.io.uvl;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;

import de.neominik.uvl.UVLParser;
import de.neominik.uvl.ast.And;
import de.neominik.uvl.ast.Equiv;
import de.neominik.uvl.ast.Feature;
import de.neominik.uvl.ast.Group;
import de.neominik.uvl.ast.Impl;
import de.neominik.uvl.ast.Not;
import de.neominik.uvl.ast.Or;
import de.neominik.uvl.ast.ParseError;
import de.neominik.uvl.ast.UVLModel;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.AFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.APersistentFormat;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.Problem.Severity;
import de.ovgu.featureide.fm.core.io.ProblemList;

/**
 * TODO description
 *
 * @author Dominik Engelhardt
 */
public class UVLFeatureModelFormat extends AFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + UVLFeatureModelFormat.class.getSimpleName();
	public static final String FILE_EXTENSION = "uvl";

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
		// TODO Auto-generated method stub
		return super.getInstance();
	}

	@Override
	public ProblemList read(IFeatureModel fm, CharSequence source) {
		final ProblemList pl = new ProblemList();
		final Object result = UVLParser.parse(source.toString());
		if (result instanceof UVLModel) {
			constructFeatureModel(fm, (UVLModel) result);
		} else if (result instanceof ParseError) {
			pl.add(toProblem((ParseError) result));
		}
		return pl;
	}

	/**
	 * @param object
	 * @param result
	 */
	private void constructFeatureModel(IFeatureModel fm, UVLModel result) {
		fm.reset();
		IFeature root;
		if (result.getRootFeatures().length == 1) {
			final Feature f = result.getRootFeatures()[0];
			root = parseFeature(fm, null, f);
		} else {
			root = MultiFeatureModelFactory.getInstance().createFeature(fm, "Root");
			List.of(result.getRootFeatures()).forEach(f -> parseFeature(fm, root, f));
		}
		fm.getStructure().setRoot(root.getStructure());
		List.of(result.getConstraints()).forEach(c -> parseConstraint(fm, c));
	}

	private IFeature parseFeature(IFeatureModel fm, IFeature root, Feature f) {
		final IFeature feature = MultiFeatureModelFactory.getInstance().createFeature(fm, f.getName());
		if (root != null) {
			root.getStructure().addChild(feature.getStructure());
		}
		feature.getStructure().setAbstract(isAbstract(f));
		List.of(f.getGroups()).forEach(g -> parseGroup(fm, feature, g));
		return feature;
	}

	/**
	 * @param fm
	 * @param root
	 * @param g
	 * @return
	 */
	private void parseGroup(IFeatureModel fm, IFeature root, Group g) {
		final List<IFeature> children = Stream.of(g.getChildren()).map(f -> parseFeature(fm, root, (Feature) f)).collect(Collectors.toList());
		switch (g.getType()) {
		case "or":
			root.getStructure().setOr();
			break;
		case "alternative":
			root.getStructure().setAlternative();
			break;
		case "optional":
			break;
		case "mandatory":
			children.forEach(f -> f.getStructure().setMandatory(true));
			break;
		}
	}

	private boolean isAbstract(Feature f) {
		return Objects.equals(true, f.getAttributes().get("abstract"));
	}

	/**
	 * @param fm
	 * @param c
	 * @return
	 */
	private void parseConstraint(IFeatureModel fm, Object c) {
		fm.addConstraint(MultiFeatureModelFactory.getInstance().createConstraint(fm, parseConstraint(c)));
	}

	private Node parseConstraint(Object c) {
		if (c instanceof String) {
			return new Literal((String) c);
		} else if (c instanceof Not) {
			return new org.prop4j.Not(parseConstraint(((Not) c).getChild()));
		} else if (c instanceof And) {
			return new org.prop4j.And(parseConstraint(((And) c).getLeft()), parseConstraint(((And) c).getRight()));
		} else if (c instanceof Or) {
			return new org.prop4j.Or(parseConstraint(((Or) c).getLeft()), parseConstraint(((Or) c).getRight()));
		} else if (c instanceof Impl) {
			return new Implies(parseConstraint(((Impl) c).getLeft()), parseConstraint(((Impl) c).getRight()));
		} else if (c instanceof Equiv) {
			return new Equals(parseConstraint(((Equiv) c).getLeft()), parseConstraint(((Equiv) c).getRight()));
		}
		return null;
	}

	/**
	 * @param error a {@link ParseError}
	 * @return a {@link Problem}
	 */
	@SuppressWarnings("unchecked")
	private Problem toProblem(ParseError error) {
		final StringBuilder sb = new StringBuilder();
		sb.append("Parse error at line ");
		sb.append(error.getLine());
		sb.append(", column ");
		sb.append(error.getColumn());
		sb.append(":\n");
		sb.append(error.getText());
		sb.append(error.getExpected().stream().collect(Collectors.joining("\n", "\nExpected one of:\n", "\n")));
		return new Problem(sb.toString(), error.getLine(), Severity.ERROR);
	}

	@Override
	public String write(IFeatureModel object) {
		// TODO implement
		return super.write(object);
	}

	@Override
	public boolean supportsRead() {
		return true;
	}

	@Override
	public boolean supportsWrite() {
		// TODO change when implemented
		return false;
	}

	@Override
	public boolean supportsContent(CharSequence content) {
		// TODO Auto-generated method stub
		return super.supportsContent(content);
	}

	@Override
	public boolean supportsContent(LazyReader reader) {
		// TODO Auto-generated method stub
		return super.supportsContent(reader);
	}

	@Override
	public boolean initExtension() {
		FMFactoryManager.getInstance().getDefaultFactoryWorkspace().assignID(getId(), MultiFeatureModelFactory.ID);
		return super.initExtension();
	}

}
