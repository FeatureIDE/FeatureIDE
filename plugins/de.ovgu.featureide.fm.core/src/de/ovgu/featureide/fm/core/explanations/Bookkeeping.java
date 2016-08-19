/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.explanations;

import java.util.ArrayList;

import org.prop4j.Literal;
import org.prop4j.Node;

/**
 * Bookkeeping is used by a logic truth maintenance system to record proofs (reasons) about variable
 * truth values set during the boolean constraint propagation.
 * 
 * @author "Ananieva Sofia"
 */
public class Bookkeeping {
	
	/**
	 * A truth value.
	 * 0 represents a false truth value, 1 represents a true truth value. 
	 * If value is -1, the truth value is yet unknown.
	 */
	public int value; 
	
	/**
	 * The reason for a derived truth value, represented by a node (which is clause in CNF).
	 */
	public Node reason; 
	
	/**
	 * Literals whose value was referenced when deriving a new truth value.
	 */
	public ArrayList<Literal> antecedents; 
	
	/**
	 * Literals whose truth values are initially set (not derived) are a premise.
	 */
	public boolean premise = false; 

	/**
	 * The value for a respective key in a hash map.
	 * 
	 * @param n The name of the literal which is key in hash map
	 * @param v The value of the literal
	 * @param r The reason for the derived truth value of the literal
	 * @param a The antecedents of the literal
	 * @param p Boolean flag whether the literal is a premise
	 */
	public Bookkeeping(int v, Node r, ArrayList<Literal> a, boolean p) {
		value = v;
		reason = r;
		antecedents = a;
		premise = p;
		
	}

}
