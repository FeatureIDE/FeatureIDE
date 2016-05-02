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

	public Object name; //name of literal, same as key in hashmap
	public int value; //0,1,-1
	public Node reason; //human-understandable formula of a clause
	public ArrayList<Literal> antecedents; //literal name which is key in bookkeeping hashmap
	public boolean premise = false; 

	public Bookkeeping(Object n, int v, Node r, ArrayList<Literal> a, boolean p) {
		name = n;
		value = v;
		reason = r;
		antecedents = a;
		premise = p;
		
	}

}
