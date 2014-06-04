/* Prop4J - A Library for Propositional Formulas
 * Copyright (C) 2007-2013  Prop4J team, University of Magdeburg, Germany
 *
 * This file is part of Prop4J.
 * 
 * Prop4J is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * Prop4J is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with Prop4J.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/prop4j/ for further information.
 */
package org.prop4j;

/**
 * Converts a propositional node to a String object.
 * 
 * @author Thomas Thuem
 */
public class NodeWriter {
	
	/**
	 * representation using logical operators
	 */
	public final static String[] logicalSymbols = new String[] {"\u00AC", " \u2227 ", " \u2228 ", " \u21D2 ", " \u21D4 ", ", ", "choose", "atleast", "atmost"};

	/**
	 * long textual representation
	 */
	public final static String[] textualSymbols = new String[] {"not ", "and", "or", "implies", "iff", ", ", "choose", "atleast", "atmost"};
	
	/**
	 * short textual representation
	 */
	public final static String[] shortSymbols = new String[] {"-", " & ", " | ", " => ", " <=> ", ", ", "choose", "atleast", "atmost"};
	
	public final static String noSymbol = " no symbol ";
	/**
	 * java textual representation
	 */
	public final static String[] javaSymbols = new String[] {"!", " && ", " || ", noSymbol, " == ", noSymbol, noSymbol, noSymbol, noSymbol};
	
	/**
	 * Converts the given node into a short textual representation.
	 * 
	 * @param node a propositional node to convert
	 * @return the textual representation
	 */
	public static String nodeToString(Node node) {
		return nodeToString(node, shortSymbols, false, null);
	}
	
	/**
	 * Converts the given node into a specified textual representation.
	 * 
	 * @param node a propositional node to convert
	 * @param symbols array containing strings for: not, and, or, implies, iff, seperator, choose, atleast and atmost
	 * @return the textual representation
	 */
	public static String nodeToString(Node node, String[] symbols) {
		return nodeToString(node, symbols, false, null);
	}

	/**
	 * Converts the given node into a specified textual representation.
	 * 
	 * @param node a propositional node to convert
	 * @param symbols array containing strings for: not, and, or, implies, iff, seperator, choose, atleast and atmost
	 * @param optionalBrackets a flag identifying if not necessary brackets will be added
	 * @return the textual representation
	 */
	public static String nodeToString(Node node, String[] symbols, boolean optionalBrackets) {
		return nodeToString(node, symbols, optionalBrackets, null);
	}


	/**
	 * Converts the given node into a specified textual representation.
	 * 
	 * @param node a propositional node to convert
	 * @param symbols array containing strings for: not, and, or, implies, iff, seperator, choose, atleast and atmost
	 * @param optionalBrackets a flag identifying if not necessary brackets will be added
	 * @param parent the class of the node's parent or null if not available
	 * @return the textual representation
	 */
	protected static String nodeToString(Node node, String[] symbols, boolean optionalBrackets, Class<? extends Node> parent)
	{
		return nodeToString(node, symbols, optionalBrackets, false, parent);
	}
	
	protected static String nodeToString(Node node, String[] symbols, boolean optionalBrackets, boolean addQuotationMarks)
	{
		return nodeToString(node, symbols, optionalBrackets, addQuotationMarks, null);
	}
	
	
	/**
	 * Converts the given node into a specified textual representation.
	 * 
	 * @param node a propositional node to convert
	 * @param symbols array containing strings for: not, and, or, implies, iff, seperator, choose, atleast and atmost
	 * @param optionalBrackets a flag identifying if not necessary brackets will be added
	 * @param parent the class of the node's parent or null if not available
	 * @param Surrounds feature name sincluding whitespaces with quotation marks
	 * @return the textual representation
	 */
	protected static String nodeToString(Node node, String[] symbols, boolean optionalBrackets, boolean addQuotationMarks, Class<? extends Node> parent) {
		if (node instanceof Literal)
		{
			if (addQuotationMarks)
			{
				String returnnode = (((Literal) node).positive ? "" : symbols[0] );
				if (((Literal) node).var.toString().contains(" "))
					returnnode += "\""  + ((Literal) node).var + "\"";
				else 
					returnnode += ((Literal) node).var;
				return returnnode;
			}else
			{
				return (((Literal) node).positive ? "" : symbols[0] ) + ((Literal) node).var;
			}
		}
		if (node instanceof Not)
			return symbols[0] + " " + nodeToString(node.getChildren()[0], symbols, optionalBrackets, addQuotationMarks, node.getClass());
		return multipleNodeToString(node, symbols, optionalBrackets, parent, addQuotationMarks);
	}

	/**
	 * Converts a node having multiple children into a specified textual representation.
	 * 
	 * @param node a propositional node to convert
	 * @param symbols array containing strings for: not, and, or, implies, iff, seperator, choose, atleast and atmost
	 * @param optionalBrackets a flag identifying if not necessary brackets will be added
	 * @param parent the class of the node's parent or null if not available
	 * @return the textual representation
	 */
	protected static String multipleNodeToString(Node node, String[] symbols, boolean optionalBrackets, Class<? extends Node> parent, boolean addQuotationMarks) {
		Node[] children = node.getChildren();
		if (children.length < 1)
			return "???";
		if (children.length == 1)
			return nodeToString(children[0], symbols, optionalBrackets,addQuotationMarks, parent);

		StringBuilder s = new StringBuilder();
		String separator = getSeparator(node, symbols);
		for (Node child : children) {
			s.append(separator);
			s.append(nodeToString(child, symbols, optionalBrackets,addQuotationMarks, node.getClass()));
		}
		
		String prefix = "";
		if (node instanceof Choose)
			prefix = symbols[6] + ((Choose) node).n;
		else if (node instanceof AtLeast)
			prefix = symbols[7] + ((AtLeast) node).min;
		else if (node instanceof AtMost)
			prefix = symbols[8] + ((AtMost) node).max;
		
		int orderParent = order(parent);
		int orderChild = order(node.getClass());
		optionalBrackets = optionalBrackets || prefix.length() > 0 || orderParent > orderChild;
		optionalBrackets |= orderParent == orderChild && orderParent == order(Implies.class);
		return prefix + (optionalBrackets ? 
					"(" + s.toString().substring(separator.length()) + ")" : 
					s.toString().substring(separator.length()));
	}
	
	/**
	 * Assigns a number to every type of node. That And has a higher order than
	 * Or means that (A and B or C) is equal to ((A and B) or C).
	 * 
	 * @param nodeClass type of node
	 * @return the order assigned to the type of node
	 */
	protected static int order(Class<? extends Node> nodeClass) {
		if (nodeClass == null)
			return 0;
		if (nodeClass.equals(AtMost.class) || nodeClass.equals(AtLeast.class) || nodeClass.equals(Choose.class))
			return 1;
		if (nodeClass.equals(Equals.class))
			return 2;
		if (nodeClass.equals(Implies.class))
			return 3;
		if (nodeClass.equals(Or.class))
			return 4;
		if (nodeClass.equals(And.class))
			return 5;
		if (nodeClass.equals(Not.class))
			return 6;
		throw new RuntimeException("Unknown subtype from org.prop4j.Node \"" + nodeClass + "\"!");
	}

	/**
	 * Retrieves the separating char between different child nodes.
	 * 
	 * @param node a node with child nodes
	 * @param symbols a textual representation
	 * @return the separating string
	 */
	protected static String getSeparator(Node node, String[] symbols) {
		if (node instanceof And)
			return " " + symbols[1] + " ";
		if (node instanceof Or)
			return " " + symbols[2] + " ";
		if (node instanceof Implies)
			return " " + symbols[3] + " ";
		if (node instanceof Equals)
			return " " + symbols[4] + " ";
		if (node instanceof Choose)
			return symbols[5];
		if (node instanceof AtLeast)
			return symbols[5];
		if (node instanceof AtMost)
			return symbols[5];
		throw new RuntimeException("Unknown subtype from org.prop4j.Node \"" + node + "\"!");
	}

}
