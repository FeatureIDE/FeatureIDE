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
package de.ovgu.featureide.featurehouse.model;

import static de.ovgu.featureide.fm.core.localization.StringTable.INVARIANT;

/**
 * Contains node types of the <code>FeatureHouse</code> internal FSTModel.
 *
 * @author Jens Meinicke
 */
public interface FHNodeTypes {

	static final String NODE_TYPE_FEATURE = "Feature";
	static final String NODE_TYPE_CLASS = "EOF Marker";
	static final String NODE_COMPILATIONUNIT = "CompilationUnit";

	// Java specific node types
	static final String JAVA_NODE_CLASS_DECLARATION = "ClassDeclaration";
	static final String JAVA_NODE_DECLARATION_TYPE1 = "ClassOrInterface1";
	static final String JAVA_NODE_DECLARATION_TYPE2 = "ClassOrInterface2";
	static final String JAVA_NODE_MODIFIERS = "Modifiers";
	static final String JAVA_NODE_FIELD = "FieldDecl";
	static final String JAVA_NODE_FIELD_2 = "ModFieldDeclaration";
	static final String JAVA_NODE_FIELD_3 = "FieldDeclaration";
	static final String JAVA_NODE_METHOD = "MethodDecl";
	static final String JAVA_NODE_CONSTRUCTOR = "ConstructorDecl";
//	static final String COMPOSITION_RULE_NAME = "JavaMethodOverriding";
	static final String JAVA_NODE_INNER_CLASS_TYPE = "InnerClassDecl";
	static final String JAVA_NODE_IMPORTDECLARATION = "ImportDeclaration";
	static final String JAVA_NODE_PACKAGEDECLARATION = "PackageDeclaration";
	static final String JAVA_NODE_IMPLEMENTATIONLIST = "ImplementsList";
	static final String JAVA_NODE_EXTENDSLIST = "ExtendsList";
	static final String JAVA_NODE_METHOD_SPEC = "MethodDeclarationWithSpec";

	// JML specific node types
	static final String JML_SPEC_CASE_SEQ = "SpecCaseSeq";
	static final String JML_INVARIANT = INVARIANT;

	// AsmetaL specific node types
	static final String ASMETAL_DOMAIN = "Domain";
	static final String ASMETAL_MODULE_DECLARATION = "ModuleDeclaration";
	static final String ASMETAL_RULE = "RuleDeclaration";
	static final String ASMETAL_FUNCTION = "Function";
	static final String ASMETAL_INVARIANT = INVARIANT;
	static final String ASMETAL_SIGNATURE = "Signature";
	static final String ASMETAL_UNNAMED_INVARIANT = "UnnamedInvariant";
	static final String ASMETAL_NAMED_INVARIANT = "NamedInvariant";
	static final String ASMETAL_INITIALIZATION = "Initialization";

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
