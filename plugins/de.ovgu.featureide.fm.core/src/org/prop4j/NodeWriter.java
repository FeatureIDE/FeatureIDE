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
package org.prop4j;

import static de.ovgu.featureide.fm.core.localization.StringTable.NO_SYMBOL;

/**
 * Converts a propositional node to a String object.
 * 
 * @author Thomas Thuem
 * @author Timo Guenther
 */
public class NodeWriter {
	/**
	 * Symbols for a logical representation.
	 * These are best used for displaying to the user due to brevity and beauty.
	 * Since they consist of unwieldy Unicode characters, do not use them for editing or serialization;
	 * in these cases, instead use {@link #textual long} or {@link #shortSymbols short textual symbols} respectively.
	 */
	public final static String[] logicalSymbols = new String[] {"\u00AC", " \u2227 ", " \u2228 ", " \u21D2 ", " \u21D4 ", ", ", "choose", "atleast", "atmost"};
	/**
	 * Symbols for a long textual representation.
	 * These are best used for editing by the user due to simplicity and ease of handling.
	 * Use {@link #logicalSymbols logical symbols} for displaying to the user and {@link #shortSymbols short textual symbols} for serialization.
	 */
	public final static String[] textualSymbols = new String[] {"not ", "and", "or", "implies", "iff", ", ", "choose", "atleast", "atmost"};
	/**
	 * Symbols for a short textual representation.
	 * Best used for serialization since they fall in the ASCII range but are still relatively short.
	 * Use {@link #logicalSymbols} for displaying to the user and {@link #textualSymbols long textual symbols} for editing by the user.
	 */
	public final static String[] shortSymbols = new String[] {"-", " & ", " | ", " => ", " <=> ", ", ", "choose", "atleast", "atmost"};
	/** Denotes an unsupported symbol. */
	public final static String noSymbol = NO_SYMBOL;
	/**
	 * Symbols for a representation like in Java.
	 * These are inherently incomplete and should only be used if absolutely necessary.
	 */
	public final static String[] javaSymbols = new String[] {"!", " && ", " || ", noSymbol, " == ", noSymbol, noSymbol, noSymbol, noSymbol};
	
	/** The propositional node to convert. */
	private final Node root;
	
	/** The symbols for the operations: not, and, or, implies, iff, separator, choose, atleast, atmost. */
	private String[] symbols = shortSymbols;
	/** If true, this writer will always place brackets, even if they are semantically irrelevant. */
	private boolean enforceBrackets = false;
	/** If true, this writer will enquote variables if they contain whitespace. */
	private boolean enquoteWhitespace = false;
	
	/**
	 * Constructs a new instance of this class with the given node to transform.
	 * By default, the set of short symbols is used, brackets are only placed if necessary, and variables containing whitespace will not be enquoted.
	 * @param propositional node to transform; not null
	 */
	public NodeWriter(Node root) {
		this.root = root;
	}
	
	/**
	 * Sets the symbols to use for the operations.
	 * By index, these are:
	 * <ol start="0">
	 * <li>{@link Not}</li>
	 * <li>{@link And}</li>
	 * <li>{@link Or}</li>
	 * <li>{@link Implies}</li>
	 * <li>{@link Equals}</li>
	 * <li>the separator joining the operands of the following operations</li>
	 * <li>{@link Choose}</li>
	 * <li>{@link AtLeast}</li>
	 * <li>{@link AtMost}</li>
	 * </ol>
	 * By default, the set of {@link shortSymbols short symbols} is used.
	 * @param symbols symbols for the operations; not null
	 * @see #logicalSymbols
	 * @see #textualSymbols
	 * @see #shortSymbols
	 * @see #javaSymbols
	 */
	public void setSymbols(String[] symbols) {
		this.symbols = symbols;
	}
	
	/**
	 * Sets the enforcing brackets flag.
	 * If true, this writer will always place brackets, even if they are semantically irrelevant. 
	 * @param enforceBrackets
	 */
	public void setEnforceBrackets(boolean enforceBrackets) {
		this.enforceBrackets = enforceBrackets;
	}
	
	/**
	 * Sets the enquoting whitespace flag.
	 * If true, this writer will enquote variables if they contain whitespace.
	 * @param enquoteWhitespace
	 */
	public void setEnquoteWhitespace(boolean enquoteWhitespace) {
		this.enquoteWhitespace = enquoteWhitespace;
	}
	
	/**
	 * Converts the given node into the specified textual representation.
	 * @return the textual representation; not null
	 */
	public String nodeToString() {
		return nodeToString(root, null);
	}
	
	/**
	 * Converts a node having at most one child into the specified textual representation.
	 * @param node propositional node to convert; not null
	 * @param parent the class of the node's parent; null if not available (i.e. the current node is the root node)
	 * @return the textual representation; not null
	 */
	protected String nodeToString(Node node, Class<? extends Node> parent) {
		if (node instanceof Literal)
		{
			if (enquoteWhitespace)
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
			return symbols[0] + " " + nodeToString(node.getChildren()[0], node.getClass());
		return multipleNodeToString(node, parent);
	}
	
	/**
	 * Converts a node having multiple children into the specified textual representation.
	 * @param node a propositional node to convert; not null
	 * @param parent the class of the node's parent; null if not available (i.e. the current node is the root node)
	 * @return the textual representation; not null
	 */
	protected String multipleNodeToString(Node node, Class<? extends Node> parent) {
		final Node[] children = node.getChildren();
		if (children.length < 1)
			return "???";
		if (children.length == 1)
			return nodeToString(children[0], parent);
		
		final String[] operands = new String[children.length];
		for (int i = 0; i < children.length; i++)
			operands[i] = nodeToString(children[i], node.getClass());
		String separated = String.join(getSeparator(node), operands);
		
		String prefix = null;
		if (node instanceof Choose)
			prefix = symbols[6] + ((Choose) node).n;
		else if (node instanceof AtLeast)
			prefix = symbols[7] + ((AtLeast) node).min;
		else if (node instanceof AtMost)
			prefix = symbols[8] + ((AtMost) node).max;
		if (prefix != null)
			return prefix + "(" + separated + ")";
		
		final int orderParent;
		final int orderChild;
		final boolean writeBrackets = enforceBrackets
				|| (orderParent = order(parent)) > (orderChild = order(node.getClass()))
				|| orderParent == orderChild && orderParent == order(Implies.class);
		if (writeBrackets)
			return "(" + separated + ")";
		return separated;
	}
	
	/**
	 * Assigns a number to every type of node.
	 * For instance, that {@link And} has a higher order than {@link Or} means that <em>(A and B or C)</em> is equal to <em>((A and B) or C)</em>.
	 * @param nodeClass type of node; not null
	 * @return the order assigned to the type of node
	 * @throws IllegalStateException if the node type is not recognized
	 */
	protected int order(Class<? extends Node> nodeClass) throws IllegalStateException {
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
		throw new IllegalStateException("Unrecognized node type: " + nodeClass);
	}
	
	/**
	 * Retrieves the string for separating the children of the given node.
	 * @param node a node with child nodes; not null
	 * @return the separating string; not null
	 * @throws IllegalStateException if the node type is not recognized
	 */
	protected String getSeparator(Node node) throws IllegalStateException {
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
		throw new IllegalStateException("Unrecognized node type: " + node);
	}
}