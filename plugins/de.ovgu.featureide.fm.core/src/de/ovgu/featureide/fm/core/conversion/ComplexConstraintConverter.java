/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.conversion;

import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * TODO description
 * 
 * @author Alexander
 */
public class ComplexConstraintConverter {
	/* Feature model factory */
	private static final IFeatureModelFactory factory = FMFactoryManager.getFactory();
	/* Working feature model */
	protected IFeatureModel fm;
	
	/**
	 * Checks whether a given node is either a requires- or an excludes-constraint
	 * @param node
	 * @return true if node is a simple constraint. False otherwise.
	 */
	public static boolean isSimple(Node node) {
		Node cnf = node.toCNF();
		if(cnf.getChildren().length == 1 && cnf.getContainedFeatures().size() == 2) {
			Node clause = cnf.getChildren()[0];
			if(clause instanceof Or) {
				Node f1 = clause.getChildren()[0];
				Node f2 = clause.getChildren()[1];

				return (f1 instanceof Literal && !((Literal)f1).positive) || (f2 instanceof Literal && !((Literal)f2).positive);
			}
		}
		return false;
	}	
	
	/**
	 * Checks whether a given node is neither a requires- nor an excludes-constraint
	 * @param node
	 * @return true if node is a complex constraint. False otherwise.
	 */
	public static boolean isComplex(Node node) {
		return !ComplexConstraintConverter.isSimple(node);
	}
	
	/**
	 * Checks whether a given node is a (hidden) composition of requires- and excludes-constraints
	 * @param node
	 * @return true if node consists of a number of simple constraints. False otherwise.
	 */
	public static boolean isPseudocomplex(Node node) {
		Node cnf = node.toCNF();
		
		if(cnf instanceof Or)
			return isSimple(node);
		
		boolean result = true;
		for(Node child : cnf.getChildren()) {
			result &= isSimple(child);
		}
		
		return result;
	}
	
	/**
	 * Eliminates complex constraints according to a given strategy.
	 * @param fm
	 * @return
	 */
	public IFeatureModel convert(IFeatureModel model, IConverterStrategy converter) {
		//check if model is valid
		if(model == null) {
			throw new IllegalArgumentException("Invalid feature model.");
		}
		
		if(converter == null) {
			throw new IllegalArgumentException("Invalid converter.");
		}
		
		//Work with a clone
		fm = model.clone();
				
		//Basic cleaning
		prepare();
		
		refactorPseudocomplexConstraints();
		
		//Get list of complex clauses and remove them from the model
		List<IConstraint> complexConstraints = pruneComplexConstraints();
		
		//Minimize constraints
		List<Node> minComplexNodes = new LinkedList<Node>();
		for(IConstraint c : complexConstraints) {			
			List<Node> nodes = converter.preprocess(c);
			
			for(Node node : nodes) {
				Node minNode = minimize(node);
				if(ComplexConstraintConverter.isSimple(minNode)) {
					fm.addConstraint(factory.createConstraint(fm, minNode));
				} else {
					minComplexNodes.add(minNode);	
				}
			}
		}
		
		if(minComplexNodes.isEmpty()) {
			return fm;
		}
		
		return converter.convert(fm, minComplexNodes, true);
	}
	
	/**
	 * 
	 * @param clause
	 * @return
	 */
	protected Node minimize(Node clause) {
		//TODO minimize complex clauses
		return clause;
	}
	
	/**
	 * Removes tautologies and redundant constraints.
	 * If the feature model is a void model or unsatisfiable then a simple contradicting feature model will be created.
	 */
	protected void prepare() {
		FeatureModelAnalyzer analyzer = fm.getAnalyser();
		
		analyzer.calculateFeatures = true;
		analyzer.calculateConstraints = true;
		analyzer.calculateRedundantConstraints = true;
		analyzer.calculateTautologyConstraints = true;
		
		analyzer.analyzeFeatureModel(null);
		List<IConstraint> toRemove = new LinkedList<IConstraint>();
		
		for (IConstraint c : fm.getConstraints()) {
			ConstraintAttribute attribute = c.getConstraintAttribute();
			
			if (attribute == ConstraintAttribute.REDUNDANT || attribute == ConstraintAttribute.TAUTOLOGY) {
				toRemove.add(c);
			} else if (attribute == ConstraintAttribute.VOID_MODEL || attribute == ConstraintAttribute.UNSATISFIABLE ) {
				IFeatureModel voidModel = factory.createFeatureModel();
				IFeature root = factory.createFeature(fm, "root");
				root.getStructure().setAbstract(true);
				voidModel.getStructure().setRoot(root.getStructure());
				voidModel.addConstraint(factory.createConstraint(fm, new Implies(root, new Not(root))));
				fm = voidModel;
				toRemove.clear();
				return;
			}
		}
	
		for (IConstraint c : toRemove) {
			fm.removeConstraint(c);
		}
	}
	
	/**
	 * Splits up a complex constraint completely into simple constraints if possible.
	 */
	protected void refactorPseudocomplexConstraints() {
		List<IConstraint> pseudocomplexConstraints = new LinkedList<IConstraint>();
		for(IConstraint c : fm.getConstraints()) {
			if(ComplexConstraintConverter.isPseudocomplex(c.getNode().clone())) {
				pseudocomplexConstraints.add(c);
			}
		}
		
		for(IConstraint c : pseudocomplexConstraints) {
			Node cnf = c.getNode().toCNF();
			if(cnf instanceof And) {
				for(Node clause : cnf.getChildren()) {
					fm.addConstraint(factory.createConstraint(fm, clause));
				}
			} else {
				fm.addConstraint(factory.createConstraint(fm, cnf));
			}
			fm.removeConstraint(c);
		}
	}
	
	/**
	 * Collects and removes all complex constraints from the feature model.
	 * @return List of complex constraints
	 */
	protected List<IConstraint> pruneComplexConstraints() {
		List<IConstraint> complexConstraints = new LinkedList<IConstraint>();
		
		for(IConstraint c : fm.getConstraints()) {
			if(ComplexConstraintConverter.isComplex(c.getNode())) {
				System.out.println("Prune: " + c.getNode());
				complexConstraints.add(c);
			}
		}
		
		for(IConstraint c : complexConstraints) {
			fm.removeConstraint(c);
		}
		
		return complexConstraints;
	}
}
