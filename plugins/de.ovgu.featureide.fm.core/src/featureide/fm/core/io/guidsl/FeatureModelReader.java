/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.fm.core.io.guidsl;

import java.io.InputStream;
import java.util.LinkedList;

import org.prop4j.And;
import org.prop4j.Choose;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.SatSolver;

import featureide.fm.core.Feature;
import featureide.fm.core.FeatureModel;
import featureide.fm.core.io.AbstractFeatureModelReader;
import featureide.fm.core.io.ModelWarning;
import featureide.fm.core.io.UnsupportedModelException;
import guidsl.AstListNode;
import guidsl.AstNode;
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
 */
public class FeatureModelReader extends AbstractFeatureModelReader {
	
	/**
	 * Needed because the GUIDSL parser uses static variables and should not
	 * be used by different threads at the same time.
	 */
	private static Object lock = new Object();
	
	/**
	 * Creates a new reader and sets the feature model to store the data.
	 * 
	 * @param featureModel the structure to fill
	 */
	public FeatureModelReader(FeatureModel featureModel) {
		setFeatureModel(featureModel);
	}

	@Override
	protected void parseInputStream(InputStream inputStream)
			throws UnsupportedModelException {
		warnings.clear();
        try {
        	synchronized (lock) {
        		Parser myParser = Parser.getInstance(inputStream);
                Model root = (Model) myParser.parseAll();
                readModelData(root);
			}
        }
        catch (ParseException e) {
        	int line = e.currentToken.next.beginLine;
        	throw new UnsupportedModelException(e.getMessage(), line);
        }
	}

	private void readModelData(Model root) throws UnsupportedModelException {
		//print("", root);
		featureModel.reset();
		featureModel.hasAbstractFeatures(!root.toString().startsWith("//NoAbstractFeatures"));
		
		Prods prods = ((MainModel) root).getProds();
		AstListNode astListNode = (AstListNode) prods.arg[0];
		do {
			readGProduction((GProduction) astListNode.arg[0]);
			astListNode = (AstListNode) astListNode.right;
		} while (astListNode != null);
		
		AstOptNode consOptNode = (AstOptNode) prods.right;
		if (consOptNode.arg.length > 0 && consOptNode.arg[0] != null)
			readConsStmt((ConsStmt) consOptNode.arg[0]);

		AstOptNode varOptNode = (AstOptNode) consOptNode.right;
		if (varOptNode.arg.length > 0 && varOptNode.arg[0] != null)
			readVarStmt((VarStmt) varOptNode.arg[0]);
		
		featureModel.handleModelDataLoaded();
	}

	private void readGProduction(GProduction gProduction) throws UnsupportedModelException {
		String name = gProduction.getIDENTIFIER().name;
		Feature feature = featureModel.getFeature(name);
		if (feature == null) 
			throw new UnsupportedModelException("The compound feature '" + name + "' have to occur on a right side of a rule before using it on a left side!", gProduction.getIDENTIFIER().lineNum());
		feature.setAND(false);
		Pats pats = gProduction.getPats();
		AstListNode astListNode = (AstListNode) pats.arg[0];
		do {
			Feature child = readPat((Pat) astListNode.arg[0]);
			feature.addChild(child);
			astListNode = (AstListNode) astListNode.right;
		} while (astListNode != null);
		simplify(feature);
	}

	private Feature readPat(Pat pat) throws UnsupportedModelException {
		if (pat instanceof GPattern)
			return readGPattern((GPattern) pat);
		SimplePattern simplePattern = (SimplePattern) pat;
		AstToken token = simplePattern.getIDENTIFIER();
		return createFeature(token);
	}

	private Feature readGPattern(GPattern gPattern) throws UnsupportedModelException {
		AstToken token = gPattern.getIDENTIFIER();
		Feature feature = createFeature(token);
		feature.setAND(true);
		TermList termList = gPattern.getTermList();
		AstListNode astListNode = (AstListNode) termList.arg[0];
		do {
			Feature child = readGTerm((GTerm) astListNode.arg[0]);
			feature.addChild(child);
			astListNode = (AstListNode) astListNode.right;
		} while (astListNode != null);
		return simplify(feature);
	}

	private Feature readGTerm(GTerm term) throws UnsupportedModelException {
		AstToken token;
		if (term instanceof PlusTerm)
			token = ((PlusTerm) term).getIDENTIFIER();
		else if (term instanceof StarTerm)
			token = ((StarTerm) term).getIDENTIFIER();
		else if (term instanceof TermName)
			token = ((TermName) term).getIDENTIFIER();
		else
			token = ((OptTerm) term).getIDENTIFIER();
		Feature feature = createFeature(token);
		feature.setMandatory(term instanceof PlusTerm || term instanceof TermName);
		feature.setMultiple(term instanceof PlusTerm || term instanceof StarTerm);
		return feature;
	}

	private Feature createFeature(AstToken token) throws UnsupportedModelException {
		Feature feature = new Feature(featureModel, token.name);
		if (!featureModel.addFeature(feature))
			throw new UnsupportedModelException("The feature '" + feature.getName() + "' occurs again on a right side of a rule and that's not allowed!", token.lineNum());
		return feature;
	}

	private Feature simplify(Feature feature) {
		if (feature.getChildrenCount() == 1) {
			Feature child = feature.getFirstChild();
			if (child.getName().equals("_" + feature.getName())) {
				feature.removeChild(child);
				feature.setChildren(child.getChildren());
				feature.setAND(child.isAnd());
				featureModel.deleteFeatureFromTable(child);
			}
			else if (feature.getName().equals(child.getName() + "_")) {
				feature.removeChild(child);
				if (feature == featureModel.getRoot())
					featureModel.replaceRoot(child);
				else
					featureModel.deleteFeatureFromTable(feature);
				feature = child;
			}
			else if (feature != featureModel.getRoot() && feature.getName().equals("_" + child.getName())) {
				feature.removeChild(child);
				featureModel.deleteFeatureFromTable(feature);
				feature = child;
			}
		}
		return feature;
	}
	
	private int line;

	private void readConsStmt(ConsStmt consStmt) throws UnsupportedModelException {
		ESList eSList = consStmt.getESList();
		AstListNode astListNode = (AstListNode) eSList.arg[0];
		do {
			line = 0;
			Node node = exprToNode(((EStmt) astListNode.arg[0]).getExpr());
			try {
				if (!new SatSolver(new Not(node.clone()), 250).isSatisfiable())
					warnings.add(new ModelWarning("Constraint is a tautology.", line));
				if (!new SatSolver(node.clone(), 250).isSatisfiable())
					warnings.add(new ModelWarning("Constraint is not satisfiable.", line));
			} catch (Exception e) {
			}
			featureModel.addPropositionalNode(node);
			astListNode = (AstListNode) astListNode.right;
		} while (astListNode != null);
	}

	private Node exprToNode(Expr expr) throws UnsupportedModelException {
		if (expr instanceof Bvar) {
			AstToken token = ((Bvar) expr).getIDENTIFIER();
			line = token.lineNum();
			String var = token.name;
			if (featureModel.getFeature(var) == null)
				throw new UnsupportedModelException("The feature '" + var + "' does not occur in the grammar!", token.lineNum());
			return new Literal(var);
		}
		if (expr instanceof Paren)
			return exprToNode(((Paren) expr).getExpr());
		if (expr instanceof BNot)
			return new Not(exprToNode(((BNot) expr).getNExpr()));
		if (expr instanceof BAnd)
			return new And(exprToNode(((BAnd) expr).getNExpr()), exprToNode(((BAnd) expr).getAExpr()));
		if (expr instanceof BOr)
			return new Or(exprToNode(((BOr) expr).getAExpr()), exprToNode(((BOr) expr).getOExpr()));
		if (expr instanceof BImplies)
			return new Implies(exprToNode(((BImplies) expr).getOExpr()), exprToNode(((BImplies) expr).getIExpr()));
		if (expr instanceof BIff)
			return new Equals(exprToNode(((BIff) expr).getIExpr()), exprToNode(((BIff) expr).getEExpr()));
		if (expr instanceof BChoose1) {
			ExprList exprList = ((BChoose1) expr).getExprList();
			AstListNode astListNode = (AstListNode) exprList.arg[0];
			LinkedList<Node> nodes = new LinkedList<Node>();
			do {
				nodes.add(exprToNode((Expr) astListNode.arg[0]));
				astListNode = (AstListNode) astListNode.right;
			} while (astListNode != null);
			return new Choose(1, nodes);
		}
		throw new RuntimeException("unsupported type in guidsl grammar");
	}

	private void readVarStmt(VarStmt varStmt) {
		featureModel.setAnnotations(varStmt.toString().trim());
		AvarList avarList = varStmt.getAvarList();
		AstListNode astListNode = (AstListNode) avarList.arg[0];
		do {
			readVar((Var) astListNode.arg[0]);
			astListNode = (AstListNode) astListNode.right;
		} while (astListNode != null);
	}

	private void readVar(Var var) {
		//TODO #31: reading annotations not yet implemented
	}

	@SuppressWarnings("unused")
	private void print(String tab, AstNode node) {
		if (node != null) {
			if (node instanceof AstListNode)
				System.out.println(tab + "AstListNode");
			else
				System.out.println(tab + node.className() + ": " + node.toString().trim().replaceAll("\\s+", " "));
			if (node.arg.length > 0)
				print(tab + "\t", node.arg[0]);
			print(tab, node.right);
		}
	}

}
