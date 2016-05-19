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

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * TODO description
 * 
 * @author Alexander
 */
public class ComplexConstraintConverter {
	private static final IFeatureModelFactory factory = FMFactoryManager.getFactory();
	
	protected IFeatureModel fm;
	
	/**
	 * Checks whether given node is either a requires- or an excludes-constraint
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
	 * Checks whether given node is neither a requires- nor an excludes-constraint
	 * @param node
	 * @return true if node is a complex constraint. False otherwise.
	 */
	public static boolean isComplex(Node node) {
		return !ComplexConstraintConverter.isSimple(node);
	}
	
	/**
	 * Eliminates complex constraints according to given strategy
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
	
	protected Node minimize(Node clause) {
		//TODO minimize complex clauses
		return clause;
	}
	
	protected void prepare() {
		//TODO remove redundant constraints or tautologies (method: prepare)
		//TODO split up clauses from complex constraints that model a simple constraint (method: prepare)
		//TODO replace requires and excludes constraint with "implication"-syntax (method: prepare)
	}
	
	protected List<IConstraint> pruneComplexConstraints() {
		List<IConstraint> complexConstraints = new LinkedList<IConstraint>();
		
		for(IConstraint c : fm.getConstraints()) {
			if(ComplexConstraintConverter.isComplex(c.getNode())) {
				complexConstraints.add(c);
			}
		}
		
		for(IConstraint c : complexConstraints) {
			fm.removeConstraint(c);
		}
		
		return complexConstraints;
	}
}
