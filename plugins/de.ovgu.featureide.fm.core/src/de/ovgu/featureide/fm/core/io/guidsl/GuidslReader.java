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
package de.ovgu.featureide.fm.core.io.guidsl;

import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_A_TAUTOLOGY_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT_IS_NOT_SATISFIABLE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.EMPTY___;
import static de.ovgu.featureide.fm.core.localization.StringTable.HIDDEN;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_COMPOUND_FEATURE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_FEATURE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.UNSUPPORTED_TYPE_IN_GUIDSL_GRAMMAR;

import java.io.StringReader;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;

import org.prop4j.And;
import org.prop4j.Choose;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.SatSolver;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.Constraint;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import guidsl.AstListNode;
import guidsl.AstOptNode;
import guidsl.AstToken;
import guidsl.AvarList;
import guidsl.BAnd;
import guidsl.BChoose1;
import guidsl.BIff;
import guidsl.BImplies;
import guidsl.BNot;
import guidsl.BOr;
import guidsl.Bvar;
import guidsl.ConsStmt;
import guidsl.ESList;
import guidsl.EStmt;
import guidsl.Expr;
import guidsl.ExprList;
import guidsl.GPattern;
import guidsl.GProduction;
import guidsl.GTerm;
import guidsl.MainModel;
import guidsl.Model;
import guidsl.OptTerm;
import guidsl.Paren;
import guidsl.ParseException;
import guidsl.Parser;
import guidsl.Pat;
import guidsl.Pats;
import guidsl.PlusTerm;
import guidsl.Prods;
import guidsl.SimplePattern;
import guidsl.StarTerm;
import guidsl.TermList;
import guidsl.TermName;
import guidsl.Var;
import guidsl.VarStmt;

/**
 * Parses the feature models in the GUIDSL format (grammar).
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class GuidslReader {

	/**
	 * Needed because the GUIDSL parser uses static variables and should not be used by different threads at the same time.
	 */
	private static Object lock = new Object();

	private final List<Integer> annLine = new LinkedList<Integer>();

	private boolean noAbstractFeatures = false;

	private IFeatureModel featureModel;
	private final ProblemList warnings = new ProblemList();

	public List<Integer> getAnnLine() {
		return Collections.unmodifiableList(annLine);
	}

	public void parseInputStream(IFeatureModel featureModel, String source) throws UnsupportedModelException {
		this.featureModel = featureModel;
		warnings.clear();
		try {
			synchronized (lock) {
				final Parser myParser = Parser.getInstance(new StringReader(source));
				final Model root = (Model) myParser.parseAll();
				readModelData(root);
			}
			featureModel.handleModelDataLoaded();
		} catch (final ParseException e) {
			final int line = e.currentToken.next.beginLine;
			throw new UnsupportedModelException(e.getMessage(), line);
		}
	}

	// converts a string with "\n" to a list of lines
	private List<String> stringToList(String str) {
		final List<String> result = new LinkedList<String>();
		while (str.contains("\n")) {
			final int ind = str.indexOf('\n');
			if (ind > 0) {
				result.add(str.substring(0, ind - 1));
			}
			str = str.substring(ind + 1);
		}
		if (str.length() > 0) {
			result.add(str);
		}
		return result;
	}

	private void readModelData(Model root) throws UnsupportedModelException {

		featureModel.reset();
		String guidsl = root.toString();

		noAbstractFeatures = (guidsl.startsWith("//NoAbstractFeatures"));

		// Reading comments
		if (noAbstractFeatures) {
			guidsl = guidsl.substring(20);
		}

		final List<String> comments = new LinkedList<String>();
		while (guidsl.contains("//")) {
			guidsl = guidsl.substring(guidsl.indexOf("//"));
			final int index = guidsl.indexOf('\n');
			if (index > 0) {
				comments.add(guidsl.substring(2, index - 1));
			} else {
				comments.add(guidsl.substring(2, guidsl.length() - 1));
			}
			guidsl = guidsl.substring(guidsl.indexOf("//") + 2);
		}

		for (int i = 0; i < comments.size(); i++) {
			featureModel.getProperty().addComment(comments.get(i));
		}

		final Prods prods = ((MainModel) root).getProds();
		AstListNode astListNode = (AstListNode) prods.arg[0];

		readGProductionRoot((GProduction) astListNode.arg[0]);
		astListNode = (AstListNode) astListNode.right;

		while (astListNode != null) {
			readGProduction((GProduction) astListNode.arg[0]);
			astListNode = (AstListNode) astListNode.right;
		}

		final AstOptNode consOptNode = (AstOptNode) prods.right;
		if ((consOptNode.arg.length > 0) && (consOptNode.arg[0] != null)) {
			readConsStmt((ConsStmt) consOptNode.arg[0]);
		}

		final AstOptNode varOptNode = (AstOptNode) consOptNode.right;
		if ((varOptNode.arg.length > 0) && (varOptNode.arg[0] != null)) {
			readVarStmt((VarStmt) varOptNode.arg[0]);
		}

		// Reading hidden features and other annotations
		final int ind = root.toString().indexOf("##");
		if (ind >= 0) {
			final String annotations = root.toString().substring(ind + 3);
			final int counter = root.toString().substring(0, root.toString().indexOf("##")).split("\n").length + 2;
			final List<String> list = stringToList(annotations);
			for (int i = 0; i < list.size(); i++) {
				final String line = list.get(i);
				if (line.contains("{")) {
					final String tempLine = line.substring(line.indexOf('{')).toLowerCase(Locale.ENGLISH);
					if (tempLine.contains(HIDDEN)) {
						final int ix = tempLine.indexOf(HIDDEN);
						final String ch = tempLine.substring(ix - 1, ix);
						if (ch.equals(" ") || ch.equals("{")) {
							final String featName = line.substring(0, line.indexOf('{') - 1);
							if (featureModel.getFeature(featName) != null) {
								featureModel.getFeature(featName).getStructure().setHidden(true);
							} else {
								throw new UnsupportedModelException(THE_FEATURE_ + featName + "' does not occur in the feature model!", 0);
							}
						} else {
							// SAVE OTHER ANNOTATIONS - Write to the comment session
							annLine.add(counter + i);
							featureModel.getProperty().addComment(line);
						}
					} else {
						// SAVE OTHER ANNOTATIONS - Write to the comment session
						annLine.add(counter + i);
						featureModel.getProperty().addComment(line);

					}
				}
			}
		}

		featureModel.handleModelDataLoaded();
	}

	private void readGProduction(GProduction gProduction, IFeature feature) throws UnsupportedModelException {
		feature.getStructure().setAND(false);
		final Pats pats = gProduction.getPats();
		AstListNode astListNode = (AstListNode) pats.arg[0];
		do {
			final IFeature child = readPat((Pat) astListNode.arg[0]);
			feature.getStructure().addChild(child.getStructure());
			feature.getStructure().setAbstract(!noAbstractFeatures);
			astListNode = (AstListNode) astListNode.right;
		} while (astListNode != null);
		simplify(feature);
	}

	private void readGProduction(GProduction gProduction) throws UnsupportedModelException {
		final String name = gProduction.getIDENTIFIER().name;
		final IFeature feature = featureModel.getFeature(gProduction.getIDENTIFIER().name);
		if (feature == null) {
			throw new UnsupportedModelException(THE_COMPOUND_FEATURE_ + name + "' have to occur on a right side of a rule before using it on a left side!",
					gProduction.getIDENTIFIER().lineNum());
		}
		readGProduction(gProduction, feature);
	}

	private void readGProductionRoot(GProduction gProduction) throws UnsupportedModelException {
		final IFeature root = new Feature(featureModel, gProduction.getIDENTIFIER().name);
		featureModel.addFeature(root);
		featureModel.getStructure().setRoot(root.getStructure());
		readGProduction(gProduction, root);
	}

	private IFeature readPat(Pat pat) throws UnsupportedModelException {
		if (pat instanceof GPattern) {
			return readGPattern((GPattern) pat);
		}
		final SimplePattern simplePattern = (SimplePattern) pat;
		final AstToken token = simplePattern.getIDENTIFIER();
		final IFeature feature = createFeature(token);
		feature.getStructure().setMandatory(true);
		return feature;
	}

	private IFeature readGPattern(GPattern gPattern) throws UnsupportedModelException {
		final AstToken token = gPattern.getIDENTIFIER();
		final IFeature feature = createFeature(token);
		feature.getStructure().setAND(true);
		final TermList termList = gPattern.getTermList();
		AstListNode astListNode = (AstListNode) termList.arg[0];
		do {
			final IFeature child = readGTerm((GTerm) astListNode.arg[0]);
			feature.getStructure().addChild(child.getStructure());
			feature.getStructure().setAbstract(!noAbstractFeatures);
			astListNode = (AstListNode) astListNode.right;
		} while (astListNode != null);
		return simplify(feature);
	}

	private IFeature readGTerm(GTerm term) throws UnsupportedModelException {
		AstToken token;
		if (term instanceof PlusTerm) {
			token = ((PlusTerm) term).getIDENTIFIER();
		} else if (term instanceof StarTerm) {
			token = ((StarTerm) term).getIDENTIFIER();
		} else if (term instanceof TermName) {
			token = ((TermName) term).getIDENTIFIER();
		} else {
			token = ((OptTerm) term).getIDENTIFIER();
		}
		final IFeature feature = createFeature(token);
		feature.getStructure().setMandatory((term instanceof PlusTerm) || (term instanceof TermName));
		feature.getStructure().setMultiple((term instanceof PlusTerm) || (term instanceof StarTerm));
		return feature;
	}

	private IFeature createFeature(AstToken token) throws UnsupportedModelException {
		final IFeature feature = new Feature(featureModel, token.name);
		if (!featureModel.addFeature(feature)) {
			throw new UnsupportedModelException(THE_FEATURE_ + feature.getName() + "' occurs again on a right side of a rule and that's not allowed!",
					token.lineNum());
		}
		return feature;
	}

	private IFeature simplify(IFeature feature) {
		if (feature.getStructure().getChildrenCount() == 1) {
			final IFeature child = feature.getStructure().getFirstChild().getFeature();
			if (child.getName().equals(EMPTY___ + feature.getName())) {
				feature.getStructure().removeChild(child.getStructure());
				feature.getStructure().setChildren(child.getStructure().getChildren());
				feature.getStructure().setAND(child.getStructure().isAnd());
				featureModel.deleteFeatureFromTable(child);
			} else if (feature.getName().equals(child.getName() + EMPTY___)) {
				feature.getStructure().removeChild(child.getStructure());
				if (feature == featureModel.getStructure().getRoot().getFeature()) {
					featureModel.getStructure().replaceRoot(child.getStructure());
				} else {
					featureModel.deleteFeatureFromTable(feature);
				}
				feature = child;
			} else if (!feature.equals(featureModel.getStructure().getRoot().getFeature()) && feature.getName().equals(EMPTY___ + child.getName())) {
				feature.getStructure().removeChild(child.getStructure());
				featureModel.deleteFeatureFromTable(feature);
				feature = child;
			}
		}
		return feature;
	}

	private int line;

	private void readConsStmt(ConsStmt consStmt) throws UnsupportedModelException {
		final ESList eSList = consStmt.getESList();
		AstListNode astListNode = (AstListNode) eSList.arg[0];
		do {
			line = 1;
			final Node node = exprToNode(((EStmt) astListNode.arg[0]).getExpr());
			try {
				if (!new SatSolver(new Not(node.clone()), 250).isSatisfiable()) {
					warnings.add(new Problem(CONSTRAINT_IS_A_TAUTOLOGY_, line));
				}
				if (!new SatSolver(node.clone(), 250).isSatisfiable()) {
					warnings.add(new Problem(CONSTRAINT_IS_NOT_SATISFIABLE_, line));
				}
			} catch (final Exception e) {}
			featureModel.addConstraint(new Constraint(featureModel, node));
			astListNode = (AstListNode) astListNode.right;
		} while (astListNode != null);
	}

	private Node exprToNode(Expr expr) throws UnsupportedModelException {
		if (expr instanceof Bvar) {
			final AstToken token = ((Bvar) expr).getIDENTIFIER();
			line = token.lineNum();
			final String var = token.name;
			if (featureModel.getFeature(var) == null) {
				throw new UnsupportedModelException(THE_FEATURE_ + var + "' does not occur in the grammar!", token.lineNum());
			}
			// return new Literal(featureModel.getFeature(var));
			return new Literal(var);
		}
		if (expr instanceof Paren) {
			return exprToNode(((Paren) expr).getExpr());
		}
		if (expr instanceof BNot) {
			return new Not(exprToNode(((BNot) expr).getNExpr()));
		}
		if (expr instanceof BAnd) {
			return new And(exprToNode(((BAnd) expr).getNExpr()), exprToNode(((BAnd) expr).getAExpr()));
		}
		if (expr instanceof BOr) {
			return new Or(exprToNode(((BOr) expr).getAExpr()), exprToNode(((BOr) expr).getOExpr()));
		}
		if (expr instanceof BImplies) {
			return new Implies(exprToNode(((BImplies) expr).getOExpr()), exprToNode(((BImplies) expr).getIExpr()));
		}
		if (expr instanceof BIff) {
			return new Equals(exprToNode(((BIff) expr).getIExpr()), exprToNode(((BIff) expr).getEExpr()));
		}
		if (expr instanceof BChoose1) {
			final ExprList exprList = ((BChoose1) expr).getExprList();
			AstListNode astListNode = (AstListNode) exprList.arg[0];
			final LinkedList<Node> nodes = new LinkedList<Node>();
			do {
				nodes.add(exprToNode((Expr) astListNode.arg[0]));
				astListNode = (AstListNode) astListNode.right;
			} while (astListNode != null);
			return new Choose(1, nodes);
		}
		throw new RuntimeException(UNSUPPORTED_TYPE_IN_GUIDSL_GRAMMAR);
	}

	private void readVarStmt(VarStmt varStmt) {
		final AvarList avarList = varStmt.getAvarList();
		AstListNode astListNode = (AstListNode) avarList.arg[0];
		do {
			readVar((Var) astListNode.arg[0]);
			astListNode = (AstListNode) astListNode.right;
		} while (astListNode != null);
	}

	private void readVar(Var var) {
		// TODO #31: reading annotations not yet implemented
	}

	public Collection<? extends Problem> getWarnings() {
		return warnings;
	}

}
