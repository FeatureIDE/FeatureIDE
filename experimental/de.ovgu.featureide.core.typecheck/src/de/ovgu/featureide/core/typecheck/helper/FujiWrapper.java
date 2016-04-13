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
package de.ovgu.featureide.core.typecheck.helper;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.apache.commons.cli.ParseException;

import AST.ASTNode;
import AST.Program;
import fuji.CompilerWarningException;
import fuji.Composition;
import fuji.FeatureDirNotFoundException;
import fuji.Main;
import fuji.SemanticErrorException;
import fuji.SyntacticErrorException;
import fuji.WrongArgumentException;

/**
 * Auxiliary class to help working with Fuji
 * 
 * @author Soenke Holthusen
 * 
 */
public class FujiWrapper {
    /**
     * Initiates the Fuju Compiler and returns an iterator over all declared
     * Programs
     * 
     * @param features
     *            the list of features to use for the composition
     * @param feature_path
     *            the path to the feature-modules
     * @return an iterator over the programs
     * @throws WrongArgumentException
     * @throws ParseException
     * @throws IOException
     * @throws FeatureDirNotFoundException
     * @throws SyntacticErrorException
     * @throws SemanticErrorException
     * @throws CompilerWarningException
     */
    public static Iterator<Program> getFujiCompositionIterator(
	    List<String> features, String feature_path)
	    throws WrongArgumentException, ParseException, IOException,
	    FeatureDirNotFoundException, SyntacticErrorException,
	    SemanticErrorException, CompilerWarningException {
	String[] fuji_options = { "-progmode", "-basedir", feature_path };

	Main m = new Main(fuji_options, features);

	Composition composition = m.getComposition(m);

	return composition.getASTIterator();
    }

    /**
     * Iterates a abstract syntax tree, searching for ASTNodes of the specific
     * type
     * 
     * @param node
     *            the current node
     * @param type
     *            the node type to look for
     * @return a list of nodes of the given type
     */
    @SuppressWarnings("rawtypes")
    public static <T> List<T> getChildNodesByType(ASTNode node, Class<T> type) {
	List<T> list = new ArrayList<T>();
	for (int i = 0; i < node.getNumChild(); i++) {
	    ASTNode c = node.getChild(i);
	    if (type.isInstance(c)) {
		list.add(type.cast(c));
	    }
	    list.addAll(getChildNodesByType(c, type));
	}
	return list;
    }

    @SuppressWarnings("rawtypes")
    public static <T> T getParentByType(ASTNode node, Class<T> type) {
	if (node == null) {
	    return null;
	}
	if (type.isInstance(node.getParent())) {
	    return type.cast(node.getParent());
	} else {
	    return getParentByType(node.getParent(), type);
	}
    }
}
