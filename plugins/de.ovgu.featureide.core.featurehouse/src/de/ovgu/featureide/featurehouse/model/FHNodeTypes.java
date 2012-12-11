/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.featurehouse.model;


/**
 * Contains node types of the <code>FeatureHouse</code> internal FSTModel.
 * @author Jens Meinicke
 */
public interface FHNodeTypes {
	static final String NODE_TYPE_FEATURE = "Feature";
	static final String NODE_TYPE_CLASS = "EOF Marker";

	// Java specific node types
	static final String JAVA_NODE_CLASS_DECLARATION = "ClassDeclaration";
	static final String JAVA_NODE_FIELD = "FieldDecl";
	static final String JAVA_NODE_METHOD = "MethodDecl";
	static final String JAVA_NODE_CONSTRUCTOR = "ConstructorDecl";
//	static final String COMPOSITION_RULE_NAME = "JavaMethodOverriding";
	static final String JAVA_NODE_INNER_CLASS_TYPE = "InnerClassDecl";

	// C specific node types
	static final String C_NODE_SEQUENCE_CODEUNIT_TOPLEVEL = "Sequence_CodeUnit_TopLevel";
	static final String C_NODE_FUNC = "Func";
//	static final String C_NODE_ID = "Id";
	static final String C_NODE_STATEMENT = "Statement";
	static final String C_NODE_STRUCTDEC = "StructDec";
//	static final Object C_NODE_TYPEDEF = "TypeDef_";
	static final String C_NODE_STMTL = "StmtTL";
	
	// C# specific node types
	static final String CSHARP_NODE_CLASS_MEMBER_DECLARATION = "class_member_declaration";
	static final String CSHARP_NODE_CLAASS_MEMBER_DECLARATION_END = "class_member_declarationEnd6";
	static final String CSHARP_NODE_COMPOSITON_METHOD = "CSharpMethodOverriding";
	static final String CSHARP_NODE_COMPOSITION_FIELD = "FieldOverriding";
	static final String CSHARP_NODE_COMPOSITION_CONSTRUCTOR = "ConstructorConcatenation";

	// Haskell specific node types
	static final String HASKELL_NODE_DECLARATION = "declaration";
	static final String HASKELL_NODE_DEFINITIONS = "definitions";
	static final String HASKELL_NODE_DATA_DECLARATION = "datadecl";
	static final String HASKELL_NODE_SIMPLE_TYPE = "simpletype";
}
