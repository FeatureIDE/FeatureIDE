// $ANTLR 3.4 Velvet.g 2016-07-17 21:07:30
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
package de.ovgu.featureide.fm.core.io.velvet;

import org.antlr.runtime.BaseRecognizer;
import org.antlr.runtime.BitSet;
import org.antlr.runtime.DFA;
import org.antlr.runtime.EarlyExitException;
import org.antlr.runtime.MismatchedSetException;
import org.antlr.runtime.NoViableAltException;
import org.antlr.runtime.Parser;
import org.antlr.runtime.ParserRuleReturnScope;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.RecognizerSharedState;
import org.antlr.runtime.Token;
import org.antlr.runtime.TokenStream;
import org.antlr.runtime.tree.CommonTreeAdaptor;
import org.antlr.runtime.tree.RewriteEarlyExitException;
import org.antlr.runtime.tree.RewriteRuleSubtreeStream;
import org.antlr.runtime.tree.RewriteRuleTokenStream;
import org.antlr.runtime.tree.Tree;
import org.antlr.runtime.tree.TreeAdaptor;

import de.ovgu.featureide.fm.core.Logger;

@SuppressWarnings({ "all", "warnings", "unchecked" })
public class VelvetParser extends Parser {

	public static final String[] tokenNames = new String[] { "<invalid>", "<EOR>", "<DOWN>", "<UP>", "ABSTRACT", "ACONSTR", "ATTR", "ATTR_OP_EQUALS",
		"ATTR_OP_GREATER", "ATTR_OP_GREATER_EQ", "ATTR_OP_LESS", "ATTR_OP_LESS_EQ", "ATTR_OP_NOT_EQUALS", "BASEEXT", "BOOLEAN", "CINTERFACE", "COLON", "COMMA",
		"CONCEPT", "CONSTR", "CONSTRAINT", "DEF", "DESCRIPTION", "EMPTY", "END_C", "END_R", "EQ", "ESC_SEQ", "EXPONENT", "FEATURE", "FLOAT", "GROUP",
		"HEX_DIGIT", "ID", "IDPath", "IMPORT", "IMPORTINSTANCE", "IMPORTINTERFACE", "INT", "MANDATORY", "MINUS", "ML_COMMENT", "OCTAL_ESC", "ONEOF", "OPERAND",
		"OP_AND", "OP_EQUIVALENT", "OP_IMPLIES", "OP_NOT", "OP_OR", "OP_XOR", "PLUS", "SEMI", "SL_COMMENT", "SOMEOF", "START_C", "START_R", "STRING", "UNARYOP",
		"UNICODE_ESC", "USE", "VAR_BOOL", "VAR_FLOAT", "VAR_INT", "VAR_STRING", "WS" };

	public static final int EOF = -1;
	public static final int ABSTRACT = 4;
	public static final int ACONSTR = 5;
	public static final int ATTR = 6;
	public static final int ATTR_OP_EQUALS = 7;
	public static final int ATTR_OP_GREATER = 8;
	public static final int ATTR_OP_GREATER_EQ = 9;
	public static final int ATTR_OP_LESS = 10;
	public static final int ATTR_OP_LESS_EQ = 11;
	public static final int ATTR_OP_NOT_EQUALS = 12;
	public static final int BASEEXT = 13;
	public static final int BOOLEAN = 14;
	public static final int CINTERFACE = 15;
	public static final int COLON = 16;
	public static final int COMMA = 17;
	public static final int CONCEPT = 18;
	public static final int CONSTR = 19;
	public static final int CONSTRAINT = 20;
	public static final int DEF = 21;
	public static final int DESCRIPTION = 22;
	public static final int EMPTY = 23;
	public static final int END_C = 24;
	public static final int END_R = 25;
	public static final int EQ = 26;
	public static final int ESC_SEQ = 27;
	public static final int EXPONENT = 28;
	public static final int FEATURE = 29;
	public static final int FLOAT = 30;
	public static final int GROUP = 31;
	public static final int HEX_DIGIT = 32;
	public static final int ID = 33;
	public static final int IDPath = 34;
	public static final int IMPORT = 35;
	public static final int IMPORTINSTANCE = 36;
	public static final int IMPORTINTERFACE = 37;
	public static final int INT = 38;
	public static final int MANDATORY = 39;
	public static final int MINUS = 40;
	public static final int ML_COMMENT = 41;
	public static final int OCTAL_ESC = 42;
	public static final int ONEOF = 43;
	public static final int OPERAND = 44;
	public static final int OP_AND = 45;
	public static final int OP_EQUIVALENT = 46;
	public static final int OP_IMPLIES = 47;
	public static final int OP_NOT = 48;
	public static final int OP_OR = 49;
	public static final int OP_XOR = 50;
	public static final int PLUS = 51;
	public static final int SEMI = 52;
	public static final int SL_COMMENT = 53;
	public static final int SOMEOF = 54;
	public static final int START_C = 55;
	public static final int START_R = 56;
	public static final int STRING = 57;
	public static final int UNARYOP = 58;
	public static final int UNICODE_ESC = 59;
	public static final int USE = 60;
	public static final int VAR_BOOL = 61;
	public static final int VAR_FLOAT = 62;
	public static final int VAR_INT = 63;
	public static final int VAR_STRING = 64;
	public static final int WS = 65;

	// delegates
	public Parser[] getDelegates() {
		return new Parser[] {};
	}

	// delegators

	public VelvetParser(TokenStream input) {
		this(input, new RecognizerSharedState());
	}

	public VelvetParser(TokenStream input, RecognizerSharedState state) {
		super(input, state);
	}

	protected TreeAdaptor adaptor = new CommonTreeAdaptor();

	public void setTreeAdaptor(TreeAdaptor adaptor) {
		this.adaptor = adaptor;
	}

	public TreeAdaptor getTreeAdaptor() {
		return adaptor;
	}

	@Override
	public String[] getTokenNames() {
		return VelvetParser.tokenNames;
	}

	@Override
	public String getGrammarFileName() {
		return "Velvet.g";
	}

	@Override
	public void emitErrorMessage(String msg) {
		Logger.logError(new Exception(msg));
	}

	@Override
	public void reportError(RecognitionException e) {
		throw new InternalSyntaxException(e);
	}

	public class InternalSyntaxException extends RuntimeException {

		private final RecognitionException e;

		public InternalSyntaxException(RecognitionException e) {
			this.e = e;
		}

		public RecognitionException getException() {
			return e;
		}
	}

	public static class velvetModel_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "velvetModel"
	// Velvet.g:93:1: velvetModel : ( imp )? ( concept | cinterface ) EOF ;
	public final VelvetParser.velvetModel_return velvetModel() throws RecognitionException {
		final VelvetParser.velvetModel_return retval = new VelvetParser.velvetModel_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token EOF4 = null;
		VelvetParser.imp_return imp1 = null;

		VelvetParser.concept_return concept2 = null;

		VelvetParser.cinterface_return cinterface3 = null;

		Tree EOF4_tree = null;

		try {
			// Velvet.g:94:2: ( ( imp )? ( concept | cinterface ) EOF )
			// Velvet.g:94:4: ( imp )? ( concept | cinterface ) EOF
			{
				root_0 = (Tree) adaptor.nil();

				// Velvet.g:94:4: ( imp )?
				int alt1 = 2;
				final int LA1_0 = input.LA(1);

				if ((LA1_0 == IMPORT)) {
					alt1 = 1;
				}
				switch (alt1) {
				case 1:
				// Velvet.g:94:4: imp
				{
					pushFollow(FOLLOW_imp_in_velvetModel472);
					imp1 = imp();

					state._fsp--;

					adaptor.addChild(root_0, imp1.getTree());

				}
					break;

				}

				// Velvet.g:94:9: ( concept | cinterface )
				int alt2 = 2;
				final int LA2_0 = input.LA(1);

				if ((LA2_0 == CONCEPT)) {
					alt2 = 1;
				} else if ((LA2_0 == CINTERFACE)) {
					alt2 = 2;
				} else {
					final NoViableAltException nvae = new NoViableAltException("", 2, 0, input);

					throw nvae;

				}
				switch (alt2) {
				case 1:
				// Velvet.g:94:10: concept
				{
					pushFollow(FOLLOW_concept_in_velvetModel476);
					concept2 = concept();

					state._fsp--;

					adaptor.addChild(root_0, concept2.getTree());

				}
					break;
				case 2:
				// Velvet.g:94:18: cinterface
				{
					pushFollow(FOLLOW_cinterface_in_velvetModel478);
					cinterface3 = cinterface();

					state._fsp--;

					adaptor.addChild(root_0, cinterface3.getTree());

				}
					break;

				}

				EOF4 = (Token) match(input, EOF, FOLLOW_EOF_in_velvetModel481);
				EOF4_tree = (Tree) adaptor.create(EOF4);
				adaptor.addChild(root_0, EOF4_tree);

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "velvetModel"

	public static class imp_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "imp"
	// Velvet.g:97:1: imp : ( IMPORT name SEMI )+ -> ^( IMPORT ( name )+ ) ;
	public final VelvetParser.imp_return imp() throws RecognitionException {
		final VelvetParser.imp_return retval = new VelvetParser.imp_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token IMPORT5 = null;
		Token SEMI7 = null;
		VelvetParser.name_return name6 = null;

		final Tree IMPORT5_tree = null;
		final Tree SEMI7_tree = null;
		final RewriteRuleTokenStream stream_IMPORT = new RewriteRuleTokenStream(adaptor, "token IMPORT");
		final RewriteRuleTokenStream stream_SEMI = new RewriteRuleTokenStream(adaptor, "token SEMI");
		final RewriteRuleSubtreeStream stream_name = new RewriteRuleSubtreeStream(adaptor, "rule name");
		try {
			// Velvet.g:98:2: ( ( IMPORT name SEMI )+ -> ^( IMPORT ( name )+ ) )
			// Velvet.g:98:4: ( IMPORT name SEMI )+
			{
				// Velvet.g:98:4: ( IMPORT name SEMI )+
				int cnt3 = 0;
				loop3: do {
					int alt3 = 2;
					final int LA3_0 = input.LA(1);

					if ((LA3_0 == IMPORT)) {
						alt3 = 1;
					}

					switch (alt3) {
					case 1:
					// Velvet.g:98:5: IMPORT name SEMI
					{
						IMPORT5 = (Token) match(input, IMPORT, FOLLOW_IMPORT_in_imp493);
						stream_IMPORT.add(IMPORT5);

						pushFollow(FOLLOW_name_in_imp495);
						name6 = name();

						state._fsp--;

						stream_name.add(name6.getTree());

						SEMI7 = (Token) match(input, SEMI, FOLLOW_SEMI_in_imp497);
						stream_SEMI.add(SEMI7);

					}
						break;

					default:
						if (cnt3 >= 1) {
							break loop3;
						}
						final EarlyExitException eee = new EarlyExitException(3, input);
						throw eee;
					}
					cnt3++;
				} while (true);

				// AST REWRITE
				// elements: IMPORT, name
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 99:2: -> ^( IMPORT ( name )+ )
				{
					// Velvet.g:99:5: ^( IMPORT ( name )+ )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(stream_IMPORT.nextNode(), root_1);

						if (!(stream_name.hasNext())) {
							throw new RewriteEarlyExitException();
						}
						while (stream_name.hasNext()) {
							adaptor.addChild(root_1, stream_name.nextTree());

						}
						stream_name.reset();

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "imp"

	public static class concept_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "concept"
	// Velvet.g:102:1: concept : CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports |
	// instanceImports )? ( definitions )? -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? ) ;
	public final VelvetParser.concept_return concept() throws RecognitionException {
		final VelvetParser.concept_return retval = new VelvetParser.concept_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token CONCEPT8 = null;
		Token ID9 = null;
		Token COLON10 = null;
		VelvetParser.conceptBaseExt_return conceptBaseExt11 = null;

		VelvetParser.instanceImports_return instanceImports12 = null;

		VelvetParser.interfaceImports_return interfaceImports13 = null;

		VelvetParser.interfaceImports_return interfaceImports14 = null;

		VelvetParser.instanceImports_return instanceImports15 = null;

		VelvetParser.interfaceImports_return interfaceImports16 = null;

		VelvetParser.instanceImports_return instanceImports17 = null;

		VelvetParser.definitions_return definitions18 = null;

		final Tree CONCEPT8_tree = null;
		final Tree ID9_tree = null;
		final Tree COLON10_tree = null;
		final RewriteRuleTokenStream stream_COLON = new RewriteRuleTokenStream(adaptor, "token COLON");
		final RewriteRuleTokenStream stream_ID = new RewriteRuleTokenStream(adaptor, "token ID");
		final RewriteRuleTokenStream stream_CONCEPT = new RewriteRuleTokenStream(adaptor, "token CONCEPT");
		final RewriteRuleSubtreeStream stream_conceptBaseExt = new RewriteRuleSubtreeStream(adaptor, "rule conceptBaseExt");
		final RewriteRuleSubtreeStream stream_instanceImports = new RewriteRuleSubtreeStream(adaptor, "rule instanceImports");
		final RewriteRuleSubtreeStream stream_interfaceImports = new RewriteRuleSubtreeStream(adaptor, "rule interfaceImports");
		final RewriteRuleSubtreeStream stream_definitions = new RewriteRuleSubtreeStream(adaptor, "rule definitions");
		try {
			// Velvet.g:103:2: ( CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports |
			// instanceImports )? ( definitions )? -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? ) )
			// Velvet.g:103:4: CONCEPT ID ( COLON conceptBaseExt )? ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports |
			// instanceImports )? ( definitions )?
			{
				CONCEPT8 = (Token) match(input, CONCEPT, FOLLOW_CONCEPT_in_concept521);
				stream_CONCEPT.add(CONCEPT8);

				ID9 = (Token) match(input, ID, FOLLOW_ID_in_concept523);
				stream_ID.add(ID9);

				// Velvet.g:104:3: ( COLON conceptBaseExt )?
				int alt4 = 2;
				final int LA4_0 = input.LA(1);

				if ((LA4_0 == COLON)) {
					alt4 = 1;
				}
				switch (alt4) {
				case 1:
				// Velvet.g:104:4: COLON conceptBaseExt
				{
					COLON10 = (Token) match(input, COLON, FOLLOW_COLON_in_concept530);
					stream_COLON.add(COLON10);

					pushFollow(FOLLOW_conceptBaseExt_in_concept532);
					conceptBaseExt11 = conceptBaseExt();

					state._fsp--;

					stream_conceptBaseExt.add(conceptBaseExt11.getTree());

				}
					break;

				}

				// Velvet.g:104:27: ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )?
				int alt5 = 5;
				alt5 = dfa5.predict(input);
				switch (alt5) {
				case 1:
				// Velvet.g:104:28: instanceImports interfaceImports
				{
					pushFollow(FOLLOW_instanceImports_in_concept537);
					instanceImports12 = instanceImports();

					state._fsp--;

					stream_instanceImports.add(instanceImports12.getTree());

					pushFollow(FOLLOW_interfaceImports_in_concept539);
					interfaceImports13 = interfaceImports();

					state._fsp--;

					stream_interfaceImports.add(interfaceImports13.getTree());

				}
					break;
				case 2:
				// Velvet.g:104:63: interfaceImports instanceImports
				{
					pushFollow(FOLLOW_interfaceImports_in_concept543);
					interfaceImports14 = interfaceImports();

					state._fsp--;

					stream_interfaceImports.add(interfaceImports14.getTree());

					pushFollow(FOLLOW_instanceImports_in_concept545);
					instanceImports15 = instanceImports();

					state._fsp--;

					stream_instanceImports.add(instanceImports15.getTree());

				}
					break;
				case 3:
				// Velvet.g:104:98: interfaceImports
				{
					pushFollow(FOLLOW_interfaceImports_in_concept549);
					interfaceImports16 = interfaceImports();

					state._fsp--;

					stream_interfaceImports.add(interfaceImports16.getTree());

				}
					break;
				case 4:
				// Velvet.g:104:117: instanceImports
				{
					pushFollow(FOLLOW_instanceImports_in_concept553);
					instanceImports17 = instanceImports();

					state._fsp--;

					stream_instanceImports.add(instanceImports17.getTree());

				}
					break;

				}

				// Velvet.g:105:3: ( definitions )?
				int alt6 = 2;
				final int LA6_0 = input.LA(1);

				if ((LA6_0 == START_C)) {
					alt6 = 1;
				}
				switch (alt6) {
				case 1:
				// Velvet.g:105:3: definitions
				{
					pushFollow(FOLLOW_definitions_in_concept560);
					definitions18 = definitions();

					state._fsp--;

					stream_definitions.add(definitions18.getTree());

				}
					break;

				}

				// AST REWRITE
				// elements: ID, definitions, interfaceImports, instanceImports, CONCEPT, conceptBaseExt
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 106:2: -> ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? )
				{
					// Velvet.g:106:5: ^( CONCEPT ID ( conceptBaseExt )? ( instanceImports )? ( interfaceImports )? ( definitions )? )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(stream_CONCEPT.nextNode(), root_1);

						adaptor.addChild(root_1, stream_ID.nextNode());

						// Velvet.g:106:18: ( conceptBaseExt )?
						if (stream_conceptBaseExt.hasNext()) {
							adaptor.addChild(root_1, stream_conceptBaseExt.nextTree());

						}
						stream_conceptBaseExt.reset();

						// Velvet.g:106:34: ( instanceImports )?
						if (stream_instanceImports.hasNext()) {
							adaptor.addChild(root_1, stream_instanceImports.nextTree());

						}
						stream_instanceImports.reset();

						// Velvet.g:106:51: ( interfaceImports )?
						if (stream_interfaceImports.hasNext()) {
							adaptor.addChild(root_1, stream_interfaceImports.nextTree());

						}
						stream_interfaceImports.reset();

						// Velvet.g:106:69: ( definitions )?
						if (stream_definitions.hasNext()) {
							adaptor.addChild(root_1, stream_definitions.nextTree());

						}
						stream_definitions.reset();

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "concept"

	public static class cinterface_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "cinterface"
	// Velvet.g:109:1: cinterface : CINTERFACE ID ( COLON conceptBaseExt )? definitions -> ^( CINTERFACE ID ( conceptBaseExt )? definitions ) ;
	public final VelvetParser.cinterface_return cinterface() throws RecognitionException {
		final VelvetParser.cinterface_return retval = new VelvetParser.cinterface_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token CINTERFACE19 = null;
		Token ID20 = null;
		Token COLON21 = null;
		VelvetParser.conceptBaseExt_return conceptBaseExt22 = null;

		VelvetParser.definitions_return definitions23 = null;

		final Tree CINTERFACE19_tree = null;
		final Tree ID20_tree = null;
		final Tree COLON21_tree = null;
		final RewriteRuleTokenStream stream_COLON = new RewriteRuleTokenStream(adaptor, "token COLON");
		final RewriteRuleTokenStream stream_ID = new RewriteRuleTokenStream(adaptor, "token ID");
		final RewriteRuleTokenStream stream_CINTERFACE = new RewriteRuleTokenStream(adaptor, "token CINTERFACE");
		final RewriteRuleSubtreeStream stream_conceptBaseExt = new RewriteRuleSubtreeStream(adaptor, "rule conceptBaseExt");
		final RewriteRuleSubtreeStream stream_definitions = new RewriteRuleSubtreeStream(adaptor, "rule definitions");
		try {
			// Velvet.g:109:12: ( CINTERFACE ID ( COLON conceptBaseExt )? definitions -> ^( CINTERFACE ID ( conceptBaseExt )? definitions ) )
			// Velvet.g:109:14: CINTERFACE ID ( COLON conceptBaseExt )? definitions
			{
				CINTERFACE19 = (Token) match(input, CINTERFACE, FOLLOW_CINTERFACE_in_cinterface593);
				stream_CINTERFACE.add(CINTERFACE19);

				ID20 = (Token) match(input, ID, FOLLOW_ID_in_cinterface595);
				stream_ID.add(ID20);

				// Velvet.g:109:29: ( COLON conceptBaseExt )?
				int alt7 = 2;
				final int LA7_0 = input.LA(1);

				if ((LA7_0 == COLON)) {
					alt7 = 1;
				}
				switch (alt7) {
				case 1:
				// Velvet.g:109:30: COLON conceptBaseExt
				{
					COLON21 = (Token) match(input, COLON, FOLLOW_COLON_in_cinterface599);
					stream_COLON.add(COLON21);

					pushFollow(FOLLOW_conceptBaseExt_in_cinterface601);
					conceptBaseExt22 = conceptBaseExt();

					state._fsp--;

					stream_conceptBaseExt.add(conceptBaseExt22.getTree());

				}
					break;

				}

				pushFollow(FOLLOW_definitions_in_cinterface605);
				definitions23 = definitions();

				state._fsp--;

				stream_definitions.add(definitions23.getTree());

				// AST REWRITE
				// elements: conceptBaseExt, ID, definitions, CINTERFACE
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 110:2: -> ^( CINTERFACE ID ( conceptBaseExt )? definitions )
				{
					// Velvet.g:110:5: ^( CINTERFACE ID ( conceptBaseExt )? definitions )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(stream_CINTERFACE.nextNode(), root_1);

						adaptor.addChild(root_1, stream_ID.nextNode());

						// Velvet.g:110:21: ( conceptBaseExt )?
						if (stream_conceptBaseExt.hasNext()) {
							adaptor.addChild(root_1, stream_conceptBaseExt.nextTree());

						}
						stream_conceptBaseExt.reset();

						adaptor.addChild(root_1, stream_definitions.nextTree());

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "cinterface"

	public static class conceptBaseExt_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "conceptBaseExt"
	// Velvet.g:113:1: conceptBaseExt : ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) ;
	public final VelvetParser.conceptBaseExt_return conceptBaseExt() throws RecognitionException {
		final VelvetParser.conceptBaseExt_return retval = new VelvetParser.conceptBaseExt_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token ID24 = null;
		Token COMMA25 = null;
		Token ID26 = null;

		final Tree ID24_tree = null;
		final Tree COMMA25_tree = null;
		final Tree ID26_tree = null;
		final RewriteRuleTokenStream stream_ID = new RewriteRuleTokenStream(adaptor, "token ID");
		final RewriteRuleTokenStream stream_COMMA = new RewriteRuleTokenStream(adaptor, "token COMMA");

		try {
			// Velvet.g:114:2: ( ID ( COMMA ID )* -> ^( BASEEXT ( ID )+ ) )
			// Velvet.g:114:4: ID ( COMMA ID )*
			{
				ID24 = (Token) match(input, ID, FOLLOW_ID_in_conceptBaseExt632);
				stream_ID.add(ID24);

				// Velvet.g:114:7: ( COMMA ID )*
				loop8: do {
					int alt8 = 2;
					final int LA8_0 = input.LA(1);

					if ((LA8_0 == COMMA)) {
						alt8 = 1;
					}

					switch (alt8) {
					case 1:
					// Velvet.g:114:8: COMMA ID
					{
						COMMA25 = (Token) match(input, COMMA, FOLLOW_COMMA_in_conceptBaseExt635);
						stream_COMMA.add(COMMA25);

						ID26 = (Token) match(input, ID, FOLLOW_ID_in_conceptBaseExt637);
						stream_ID.add(ID26);

					}
						break;

					default:
						break loop8;
					}
				} while (true);

				// AST REWRITE
				// elements: ID
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 115:2: -> ^( BASEEXT ( ID )+ )
				{
					// Velvet.g:115:5: ^( BASEEXT ( ID )+ )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(adaptor.create(BASEEXT, "BASEEXT"), root_1);

						if (!(stream_ID.hasNext())) {
							throw new RewriteEarlyExitException();
						}
						while (stream_ID.hasNext()) {
							adaptor.addChild(root_1, stream_ID.nextNode());

						}
						stream_ID.reset();

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "conceptBaseExt"

	public static class instanceImports_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "instanceImports"
	// Velvet.g:118:1: instanceImports : IMPORTINSTANCE ID name ( COMMA ID name )* -> ^( IMPORTINSTANCE ( ID name )+ ) ;
	public final VelvetParser.instanceImports_return instanceImports() throws RecognitionException {
		final VelvetParser.instanceImports_return retval = new VelvetParser.instanceImports_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token IMPORTINSTANCE27 = null;
		Token ID28 = null;
		Token COMMA30 = null;
		Token ID31 = null;
		VelvetParser.name_return name29 = null;

		VelvetParser.name_return name32 = null;

		final Tree IMPORTINSTANCE27_tree = null;
		final Tree ID28_tree = null;
		final Tree COMMA30_tree = null;
		final Tree ID31_tree = null;
		final RewriteRuleTokenStream stream_ID = new RewriteRuleTokenStream(adaptor, "token ID");
		final RewriteRuleTokenStream stream_COMMA = new RewriteRuleTokenStream(adaptor, "token COMMA");
		final RewriteRuleTokenStream stream_IMPORTINSTANCE = new RewriteRuleTokenStream(adaptor, "token IMPORTINSTANCE");
		final RewriteRuleSubtreeStream stream_name = new RewriteRuleSubtreeStream(adaptor, "rule name");
		try {
			// Velvet.g:119:2: ( IMPORTINSTANCE ID name ( COMMA ID name )* -> ^( IMPORTINSTANCE ( ID name )+ ) )
			// Velvet.g:119:4: IMPORTINSTANCE ID name ( COMMA ID name )*
			{
				IMPORTINSTANCE27 = (Token) match(input, IMPORTINSTANCE, FOLLOW_IMPORTINSTANCE_in_instanceImports662);
				stream_IMPORTINSTANCE.add(IMPORTINSTANCE27);

				ID28 = (Token) match(input, ID, FOLLOW_ID_in_instanceImports664);
				stream_ID.add(ID28);

				pushFollow(FOLLOW_name_in_instanceImports666);
				name29 = name();

				state._fsp--;

				stream_name.add(name29.getTree());

				// Velvet.g:119:27: ( COMMA ID name )*
				loop9: do {
					int alt9 = 2;
					final int LA9_0 = input.LA(1);

					if ((LA9_0 == COMMA)) {
						alt9 = 1;
					}

					switch (alt9) {
					case 1:
					// Velvet.g:119:28: COMMA ID name
					{
						COMMA30 = (Token) match(input, COMMA, FOLLOW_COMMA_in_instanceImports669);
						stream_COMMA.add(COMMA30);

						ID31 = (Token) match(input, ID, FOLLOW_ID_in_instanceImports671);
						stream_ID.add(ID31);

						pushFollow(FOLLOW_name_in_instanceImports673);
						name32 = name();

						state._fsp--;

						stream_name.add(name32.getTree());

					}
						break;

					default:
						break loop9;
					}
				} while (true);

				// AST REWRITE
				// elements: ID, name, IMPORTINSTANCE
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 120:2: -> ^( IMPORTINSTANCE ( ID name )+ )
				{
					// Velvet.g:120:5: ^( IMPORTINSTANCE ( ID name )+ )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(stream_IMPORTINSTANCE.nextNode(), root_1);

						if (!(stream_ID.hasNext() || stream_name.hasNext())) {
							throw new RewriteEarlyExitException();
						}
						while (stream_ID.hasNext() || stream_name.hasNext()) {
							adaptor.addChild(root_1, stream_ID.nextNode());

							adaptor.addChild(root_1, stream_name.nextTree());

						}
						stream_ID.reset();
						stream_name.reset();

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "instanceImports"

	public static class interfaceImports_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "interfaceImports"
	// Velvet.g:123:1: interfaceImports : IMPORTINTERFACE ID name ( COMMA ID name )* -> ^( IMPORTINTERFACE ( ID name )+ ) ;
	public final VelvetParser.interfaceImports_return interfaceImports() throws RecognitionException {
		final VelvetParser.interfaceImports_return retval = new VelvetParser.interfaceImports_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token IMPORTINTERFACE33 = null;
		Token ID34 = null;
		Token COMMA36 = null;
		Token ID37 = null;
		VelvetParser.name_return name35 = null;

		VelvetParser.name_return name38 = null;

		final Tree IMPORTINTERFACE33_tree = null;
		final Tree ID34_tree = null;
		final Tree COMMA36_tree = null;
		final Tree ID37_tree = null;
		final RewriteRuleTokenStream stream_ID = new RewriteRuleTokenStream(adaptor, "token ID");
		final RewriteRuleTokenStream stream_COMMA = new RewriteRuleTokenStream(adaptor, "token COMMA");
		final RewriteRuleTokenStream stream_IMPORTINTERFACE = new RewriteRuleTokenStream(adaptor, "token IMPORTINTERFACE");
		final RewriteRuleSubtreeStream stream_name = new RewriteRuleSubtreeStream(adaptor, "rule name");
		try {
			// Velvet.g:124:2: ( IMPORTINTERFACE ID name ( COMMA ID name )* -> ^( IMPORTINTERFACE ( ID name )+ ) )
			// Velvet.g:124:4: IMPORTINTERFACE ID name ( COMMA ID name )*
			{
				IMPORTINTERFACE33 = (Token) match(input, IMPORTINTERFACE, FOLLOW_IMPORTINTERFACE_in_interfaceImports702);
				stream_IMPORTINTERFACE.add(IMPORTINTERFACE33);

				ID34 = (Token) match(input, ID, FOLLOW_ID_in_interfaceImports704);
				stream_ID.add(ID34);

				pushFollow(FOLLOW_name_in_interfaceImports706);
				name35 = name();

				state._fsp--;

				stream_name.add(name35.getTree());

				// Velvet.g:124:28: ( COMMA ID name )*
				loop10: do {
					int alt10 = 2;
					final int LA10_0 = input.LA(1);

					if ((LA10_0 == COMMA)) {
						alt10 = 1;
					}

					switch (alt10) {
					case 1:
					// Velvet.g:124:29: COMMA ID name
					{
						COMMA36 = (Token) match(input, COMMA, FOLLOW_COMMA_in_interfaceImports709);
						stream_COMMA.add(COMMA36);

						ID37 = (Token) match(input, ID, FOLLOW_ID_in_interfaceImports711);
						stream_ID.add(ID37);

						pushFollow(FOLLOW_name_in_interfaceImports713);
						name38 = name();

						state._fsp--;

						stream_name.add(name38.getTree());

					}
						break;

					default:
						break loop10;
					}
				} while (true);

				// AST REWRITE
				// elements: IMPORTINTERFACE, name, ID
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 125:2: -> ^( IMPORTINTERFACE ( ID name )+ )
				{
					// Velvet.g:125:5: ^( IMPORTINTERFACE ( ID name )+ )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(stream_IMPORTINTERFACE.nextNode(), root_1);

						if (!(stream_name.hasNext() || stream_ID.hasNext())) {
							throw new RewriteEarlyExitException();
						}
						while (stream_name.hasNext() || stream_ID.hasNext()) {
							adaptor.addChild(root_1, stream_ID.nextNode());

							adaptor.addChild(root_1, stream_name.nextTree());

						}
						stream_name.reset();
						stream_ID.reset();

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "interfaceImports"

	public static class name_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "name"
	// Velvet.g:128:1: name : ( ID | IDPath );
	public final VelvetParser.name_return name() throws RecognitionException {
		final VelvetParser.name_return retval = new VelvetParser.name_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token set39 = null;

		final Tree set39_tree = null;

		try {
			// Velvet.g:128:5: ( ID | IDPath )
			// Velvet.g:
			{
				root_0 = (Tree) adaptor.nil();

				set39 = input.LT(1);

				if (((input.LA(1) >= ID) && (input.LA(1) <= IDPath))) {
					input.consume();
					adaptor.addChild(root_0, adaptor.create(set39));
					state.errorRecovery = false;
				} else {
					final MismatchedSetException mse = new MismatchedSetException(null, input);
					throw mse;
				}

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "name"

	public static class definitions_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "definitions"
	// Velvet.g:132:1: definitions : START_C definition END_C -> ^( DEF ( definition )? EMPTY ) ;
	public final VelvetParser.definitions_return definitions() throws RecognitionException {
		final VelvetParser.definitions_return retval = new VelvetParser.definitions_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token START_C40 = null;
		Token END_C42 = null;
		VelvetParser.definition_return definition41 = null;

		final Tree START_C40_tree = null;
		final Tree END_C42_tree = null;
		final RewriteRuleTokenStream stream_END_C = new RewriteRuleTokenStream(adaptor, "token END_C");
		final RewriteRuleTokenStream stream_START_C = new RewriteRuleTokenStream(adaptor, "token START_C");
		final RewriteRuleSubtreeStream stream_definition = new RewriteRuleSubtreeStream(adaptor, "rule definition");
		try {
			// Velvet.g:133:2: ( START_C definition END_C -> ^( DEF ( definition )? EMPTY ) )
			// Velvet.g:133:4: START_C definition END_C
			{
				START_C40 = (Token) match(input, START_C, FOLLOW_START_C_in_definitions757);
				stream_START_C.add(START_C40);

				pushFollow(FOLLOW_definition_in_definitions759);
				definition41 = definition();

				state._fsp--;

				stream_definition.add(definition41.getTree());

				END_C42 = (Token) match(input, END_C, FOLLOW_END_C_in_definitions761);
				stream_END_C.add(END_C42);

				// AST REWRITE
				// elements: definition
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 134:2: -> ^( DEF ( definition )? EMPTY )
				{
					// Velvet.g:134:5: ^( DEF ( definition )? EMPTY )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(adaptor.create(DEF, "DEF"), root_1);

						// Velvet.g:134:11: ( definition )?
						if (stream_definition.hasNext()) {
							adaptor.addChild(root_1, stream_definition.nextTree());

						}
						stream_definition.reset();

						adaptor.addChild(root_1, adaptor.create(EMPTY, "EMPTY"));

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "definitions"

	public static class definition_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "definition"
	// Velvet.g:137:1: definition : ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
	// ;
	public final VelvetParser.definition_return definition() throws RecognitionException {
		final VelvetParser.definition_return retval = new VelvetParser.definition_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		VelvetParser.nonFeatureDefinition_return nonFeatureDefinition43 = null;

		VelvetParser.featureGroup_return featureGroup44 = null;

		VelvetParser.nonFeatureDefinition_return nonFeatureDefinition45 = null;

		VelvetParser.feature_return feature46 = null;

		VelvetParser.feature_return feature47 = null;

		VelvetParser.nonFeatureDefinition_return nonFeatureDefinition48 = null;

		try {
			// Velvet.g:138:2: ( ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )? )
			// Velvet.g:138:4: ( nonFeatureDefinition )* ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
			{
				root_0 = (Tree) adaptor.nil();

				// Velvet.g:138:4: ( nonFeatureDefinition )*
				loop11: do {
					int alt11 = 2;
					final int LA11_0 = input.LA(1);

					if (((LA11_0 == CONSTRAINT) || (LA11_0 == DESCRIPTION) || ((LA11_0 >= USE) && (LA11_0 <= VAR_STRING)))) {
						alt11 = 1;
					}

					switch (alt11) {
					case 1:
					// Velvet.g:138:4: nonFeatureDefinition
					{
						pushFollow(FOLLOW_nonFeatureDefinition_in_definition785);
						nonFeatureDefinition43 = nonFeatureDefinition();

						state._fsp--;

						adaptor.addChild(root_0, nonFeatureDefinition43.getTree());

					}
						break;

					default:
						break loop11;
					}
				} while (true);

				// Velvet.g:138:26: ( ( featureGroup ( nonFeatureDefinition )* ) | ( feature ( feature | nonFeatureDefinition )* ) )?
				int alt14 = 3;
				final int LA14_0 = input.LA(1);

				if (((LA14_0 == ONEOF) || (LA14_0 == SOMEOF))) {
					alt14 = 1;
				} else if (((LA14_0 == ABSTRACT) || (LA14_0 == FEATURE) || (LA14_0 == MANDATORY))) {
					alt14 = 2;
				}
				switch (alt14) {
				case 1:
				// Velvet.g:139:3: ( featureGroup ( nonFeatureDefinition )* )
				{
					// Velvet.g:139:3: ( featureGroup ( nonFeatureDefinition )* )
					// Velvet.g:139:4: featureGroup ( nonFeatureDefinition )*
					{
						pushFollow(FOLLOW_featureGroup_in_definition793);
						featureGroup44 = featureGroup();

						state._fsp--;

						adaptor.addChild(root_0, featureGroup44.getTree());

						// Velvet.g:139:17: ( nonFeatureDefinition )*
						loop12: do {
							int alt12 = 2;
							final int LA12_0 = input.LA(1);

							if (((LA12_0 == CONSTRAINT) || (LA12_0 == DESCRIPTION) || ((LA12_0 >= USE) && (LA12_0 <= VAR_STRING)))) {
								alt12 = 1;
							}

							switch (alt12) {
							case 1:
							// Velvet.g:139:17: nonFeatureDefinition
							{
								pushFollow(FOLLOW_nonFeatureDefinition_in_definition795);
								nonFeatureDefinition45 = nonFeatureDefinition();

								state._fsp--;

								adaptor.addChild(root_0, nonFeatureDefinition45.getTree());

							}
								break;

							default:
								break loop12;
							}
						} while (true);

					}

				}
					break;
				case 2:
				// Velvet.g:139:42: ( feature ( feature | nonFeatureDefinition )* )
				{
					// Velvet.g:139:42: ( feature ( feature | nonFeatureDefinition )* )
					// Velvet.g:139:43: feature ( feature | nonFeatureDefinition )*
					{
						pushFollow(FOLLOW_feature_in_definition802);
						feature46 = feature();

						state._fsp--;

						adaptor.addChild(root_0, feature46.getTree());

						// Velvet.g:139:51: ( feature | nonFeatureDefinition )*
						loop13: do {
							int alt13 = 3;
							final int LA13_0 = input.LA(1);

							if (((LA13_0 == ABSTRACT) || (LA13_0 == FEATURE) || (LA13_0 == MANDATORY))) {
								alt13 = 1;
							} else if (((LA13_0 == CONSTRAINT) || (LA13_0 == DESCRIPTION) || ((LA13_0 >= USE) && (LA13_0 <= VAR_STRING)))) {
								alt13 = 2;
							}

							switch (alt13) {
							case 1:
							// Velvet.g:139:52: feature
							{
								pushFollow(FOLLOW_feature_in_definition805);
								feature47 = feature();

								state._fsp--;

								adaptor.addChild(root_0, feature47.getTree());

							}
								break;
							case 2:
							// Velvet.g:139:62: nonFeatureDefinition
							{
								pushFollow(FOLLOW_nonFeatureDefinition_in_definition809);
								nonFeatureDefinition48 = nonFeatureDefinition();

								state._fsp--;

								adaptor.addChild(root_0, nonFeatureDefinition48.getTree());

							}
								break;

							default:
								break loop13;
							}
						} while (true);

					}

				}
					break;

				}

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "definition"

	public static class nonFeatureDefinition_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "nonFeatureDefinition"
	// Velvet.g:143:1: nonFeatureDefinition : ( constraint | use | attribute | description );
	public final VelvetParser.nonFeatureDefinition_return nonFeatureDefinition() throws RecognitionException {
		final VelvetParser.nonFeatureDefinition_return retval = new VelvetParser.nonFeatureDefinition_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		VelvetParser.constraint_return constraint49 = null;

		VelvetParser.use_return use50 = null;

		VelvetParser.attribute_return attribute51 = null;

		VelvetParser.description_return description52 = null;

		try {
			// Velvet.g:144:2: ( constraint | use | attribute | description )
			int alt15 = 4;
			switch (input.LA(1)) {
			case CONSTRAINT: {
				alt15 = 1;
			}
				break;
			case USE: {
				alt15 = 2;
			}
				break;
			case VAR_BOOL:
			case VAR_FLOAT:
			case VAR_INT:
			case VAR_STRING: {
				alt15 = 3;
			}
				break;
			case DESCRIPTION: {
				alt15 = 4;
			}
				break;
			default:
				final NoViableAltException nvae = new NoViableAltException("", 15, 0, input);

				throw nvae;

			}

			switch (alt15) {
			case 1:
			// Velvet.g:144:4: constraint
			{
				root_0 = (Tree) adaptor.nil();

				pushFollow(FOLLOW_constraint_in_nonFeatureDefinition831);
				constraint49 = constraint();

				state._fsp--;

				adaptor.addChild(root_0, constraint49.getTree());

			}
				break;
			case 2:
			// Velvet.g:145:4: use
			{
				root_0 = (Tree) adaptor.nil();

				pushFollow(FOLLOW_use_in_nonFeatureDefinition836);
				use50 = use();

				state._fsp--;

				adaptor.addChild(root_0, use50.getTree());

			}
				break;
			case 3:
			// Velvet.g:146:4: attribute
			{
				root_0 = (Tree) adaptor.nil();

				pushFollow(FOLLOW_attribute_in_nonFeatureDefinition841);
				attribute51 = attribute();

				state._fsp--;

				adaptor.addChild(root_0, attribute51.getTree());

			}
				break;
			case 4:
			// Velvet.g:147:4: description
			{
				root_0 = (Tree) adaptor.nil();

				pushFollow(FOLLOW_description_in_nonFeatureDefinition847);
				description52 = description();

				state._fsp--;

				adaptor.addChild(root_0, description52.getTree());

			}
				break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "nonFeatureDefinition"

	public static class use_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "use"
	// Velvet.g:150:1: use : USE name SEMI -> ^( USE name ) ;
	public final VelvetParser.use_return use() throws RecognitionException {
		final VelvetParser.use_return retval = new VelvetParser.use_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token USE53 = null;
		Token SEMI55 = null;
		VelvetParser.name_return name54 = null;

		final Tree USE53_tree = null;
		final Tree SEMI55_tree = null;
		final RewriteRuleTokenStream stream_USE = new RewriteRuleTokenStream(adaptor, "token USE");
		final RewriteRuleTokenStream stream_SEMI = new RewriteRuleTokenStream(adaptor, "token SEMI");
		final RewriteRuleSubtreeStream stream_name = new RewriteRuleSubtreeStream(adaptor, "rule name");
		try {
			// Velvet.g:150:5: ( USE name SEMI -> ^( USE name ) )
			// Velvet.g:150:7: USE name SEMI
			{
				USE53 = (Token) match(input, USE, FOLLOW_USE_in_use858);
				stream_USE.add(USE53);

				pushFollow(FOLLOW_name_in_use860);
				name54 = name();

				state._fsp--;

				stream_name.add(name54.getTree());

				SEMI55 = (Token) match(input, SEMI, FOLLOW_SEMI_in_use862);
				stream_SEMI.add(SEMI55);

				// AST REWRITE
				// elements: name, USE
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 151:2: -> ^( USE name )
				{
					// Velvet.g:151:5: ^( USE name )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(stream_USE.nextNode(), root_1);

						adaptor.addChild(root_1, stream_name.nextTree());

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "use"

	public static class feature_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "feature"
	// Velvet.g:154:1: feature : ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEATURE name (
	// MANDATORY )? ( ABSTRACT )? ( definitions )? ) ;
	public final VelvetParser.feature_return feature() throws RecognitionException {
		final VelvetParser.feature_return retval = new VelvetParser.feature_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token MANDATORY56 = null;
		Token ABSTRACT57 = null;
		Token ABSTRACT58 = null;
		Token MANDATORY59 = null;
		Token MANDATORY60 = null;
		Token ABSTRACT61 = null;
		Token FEATURE62 = null;
		Token SEMI65 = null;
		VelvetParser.name_return name63 = null;

		VelvetParser.definitions_return definitions64 = null;

		final Tree MANDATORY56_tree = null;
		final Tree ABSTRACT57_tree = null;
		final Tree ABSTRACT58_tree = null;
		final Tree MANDATORY59_tree = null;
		final Tree MANDATORY60_tree = null;
		final Tree ABSTRACT61_tree = null;
		final Tree FEATURE62_tree = null;
		final Tree SEMI65_tree = null;
		final RewriteRuleTokenStream stream_ABSTRACT = new RewriteRuleTokenStream(adaptor, "token ABSTRACT");
		final RewriteRuleTokenStream stream_MANDATORY = new RewriteRuleTokenStream(adaptor, "token MANDATORY");
		final RewriteRuleTokenStream stream_SEMI = new RewriteRuleTokenStream(adaptor, "token SEMI");
		final RewriteRuleTokenStream stream_FEATURE = new RewriteRuleTokenStream(adaptor, "token FEATURE");
		final RewriteRuleSubtreeStream stream_name = new RewriteRuleSubtreeStream(adaptor, "rule name");
		final RewriteRuleSubtreeStream stream_definitions = new RewriteRuleSubtreeStream(adaptor, "rule definitions");
		try {
			// Velvet.g:155:2: ( ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI ) -> ^( FEATURE name (
			// MANDATORY )? ( ABSTRACT )? ( definitions )? ) )
			// Velvet.g:155:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )? FEATURE name ( definitions | SEMI )
			{
				// Velvet.g:155:4: ( MANDATORY ABSTRACT | ABSTRACT MANDATORY | MANDATORY | ABSTRACT )?
				int alt16 = 5;
				final int LA16_0 = input.LA(1);

				if ((LA16_0 == MANDATORY)) {
					final int LA16_1 = input.LA(2);

					if ((LA16_1 == ABSTRACT)) {
						alt16 = 1;
					} else if ((LA16_1 == FEATURE)) {
						alt16 = 3;
					}
				} else if ((LA16_0 == ABSTRACT)) {
					final int LA16_2 = input.LA(2);

					if ((LA16_2 == MANDATORY)) {
						alt16 = 2;
					} else if ((LA16_2 == FEATURE)) {
						alt16 = 4;
					}
				}
				switch (alt16) {
				case 1:
				// Velvet.g:155:5: MANDATORY ABSTRACT
				{
					MANDATORY56 = (Token) match(input, MANDATORY, FOLLOW_MANDATORY_in_feature883);
					stream_MANDATORY.add(MANDATORY56);

					ABSTRACT57 = (Token) match(input, ABSTRACT, FOLLOW_ABSTRACT_in_feature885);
					stream_ABSTRACT.add(ABSTRACT57);

				}
					break;
				case 2:
				// Velvet.g:155:26: ABSTRACT MANDATORY
				{
					ABSTRACT58 = (Token) match(input, ABSTRACT, FOLLOW_ABSTRACT_in_feature889);
					stream_ABSTRACT.add(ABSTRACT58);

					MANDATORY59 = (Token) match(input, MANDATORY, FOLLOW_MANDATORY_in_feature891);
					stream_MANDATORY.add(MANDATORY59);

				}
					break;
				case 3:
				// Velvet.g:155:47: MANDATORY
				{
					MANDATORY60 = (Token) match(input, MANDATORY, FOLLOW_MANDATORY_in_feature895);
					stream_MANDATORY.add(MANDATORY60);

				}
					break;
				case 4:
				// Velvet.g:155:59: ABSTRACT
				{
					ABSTRACT61 = (Token) match(input, ABSTRACT, FOLLOW_ABSTRACT_in_feature899);
					stream_ABSTRACT.add(ABSTRACT61);

				}
					break;

				}

				FEATURE62 = (Token) match(input, FEATURE, FOLLOW_FEATURE_in_feature906);
				stream_FEATURE.add(FEATURE62);

				pushFollow(FOLLOW_name_in_feature908);
				name63 = name();

				state._fsp--;

				stream_name.add(name63.getTree());

				// Velvet.g:156:17: ( definitions | SEMI )
				int alt17 = 2;
				final int LA17_0 = input.LA(1);

				if ((LA17_0 == START_C)) {
					alt17 = 1;
				} else if ((LA17_0 == SEMI)) {
					alt17 = 2;
				} else {
					final NoViableAltException nvae = new NoViableAltException("", 17, 0, input);

					throw nvae;

				}
				switch (alt17) {
				case 1:
				// Velvet.g:156:18: definitions
				{
					pushFollow(FOLLOW_definitions_in_feature911);
					definitions64 = definitions();

					state._fsp--;

					stream_definitions.add(definitions64.getTree());

				}
					break;
				case 2:
				// Velvet.g:156:32: SEMI
				{
					SEMI65 = (Token) match(input, SEMI, FOLLOW_SEMI_in_feature915);
					stream_SEMI.add(SEMI65);

				}
					break;

				}

				// AST REWRITE
				// elements: definitions, MANDATORY, ABSTRACT, FEATURE, name
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 157:2: -> ^( FEATURE name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
				{
					// Velvet.g:157:5: ^( FEATURE name ( MANDATORY )? ( ABSTRACT )? ( definitions )? )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(stream_FEATURE.nextNode(), root_1);

						adaptor.addChild(root_1, stream_name.nextTree());

						// Velvet.g:157:20: ( MANDATORY )?
						if (stream_MANDATORY.hasNext()) {
							adaptor.addChild(root_1, stream_MANDATORY.nextNode());

						}
						stream_MANDATORY.reset();

						// Velvet.g:157:31: ( ABSTRACT )?
						if (stream_ABSTRACT.hasNext()) {
							adaptor.addChild(root_1, stream_ABSTRACT.nextNode());

						}
						stream_ABSTRACT.reset();

						// Velvet.g:157:41: ( definitions )?
						if (stream_definitions.hasNext()) {
							adaptor.addChild(root_1, stream_definitions.nextTree());

						}
						stream_definitions.reset();

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "feature"

	public static class featureGroup_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "featureGroup"
	// Velvet.g:160:1: featureGroup : groupType START_C ( feature )+ END_C -> ^( GROUP groupType ( feature )+ ) ;
	public final VelvetParser.featureGroup_return featureGroup() throws RecognitionException {
		final VelvetParser.featureGroup_return retval = new VelvetParser.featureGroup_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token START_C67 = null;
		Token END_C69 = null;
		VelvetParser.groupType_return groupType66 = null;

		VelvetParser.feature_return feature68 = null;

		final Tree START_C67_tree = null;
		final Tree END_C69_tree = null;
		final RewriteRuleTokenStream stream_END_C = new RewriteRuleTokenStream(adaptor, "token END_C");
		final RewriteRuleTokenStream stream_START_C = new RewriteRuleTokenStream(adaptor, "token START_C");
		final RewriteRuleSubtreeStream stream_groupType = new RewriteRuleSubtreeStream(adaptor, "rule groupType");
		final RewriteRuleSubtreeStream stream_feature = new RewriteRuleSubtreeStream(adaptor, "rule feature");
		try {
			// Velvet.g:161:2: ( groupType START_C ( feature )+ END_C -> ^( GROUP groupType ( feature )+ ) )
			// Velvet.g:161:4: groupType START_C ( feature )+ END_C
			{
				pushFollow(FOLLOW_groupType_in_featureGroup946);
				groupType66 = groupType();

				state._fsp--;

				stream_groupType.add(groupType66.getTree());

				START_C67 = (Token) match(input, START_C, FOLLOW_START_C_in_featureGroup948);
				stream_START_C.add(START_C67);

				// Velvet.g:161:22: ( feature )+
				int cnt18 = 0;
				loop18: do {
					int alt18 = 2;
					final int LA18_0 = input.LA(1);

					if (((LA18_0 == ABSTRACT) || (LA18_0 == FEATURE) || (LA18_0 == MANDATORY))) {
						alt18 = 1;
					}

					switch (alt18) {
					case 1:
					// Velvet.g:161:22: feature
					{
						pushFollow(FOLLOW_feature_in_featureGroup950);
						feature68 = feature();

						state._fsp--;

						stream_feature.add(feature68.getTree());

					}
						break;

					default:
						if (cnt18 >= 1) {
							break loop18;
						}
						final EarlyExitException eee = new EarlyExitException(18, input);
						throw eee;
					}
					cnt18++;
				} while (true);

				END_C69 = (Token) match(input, END_C, FOLLOW_END_C_in_featureGroup953);
				stream_END_C.add(END_C69);

				// AST REWRITE
				// elements: feature, groupType
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 162:2: -> ^( GROUP groupType ( feature )+ )
				{
					// Velvet.g:162:5: ^( GROUP groupType ( feature )+ )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(adaptor.create(GROUP, "GROUP"), root_1);

						adaptor.addChild(root_1, stream_groupType.nextTree());

						if (!(stream_feature.hasNext())) {
							throw new RewriteEarlyExitException();
						}
						while (stream_feature.hasNext()) {
							adaptor.addChild(root_1, stream_feature.nextTree());

						}
						stream_feature.reset();

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "featureGroup"

	public static class groupType_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "groupType"
	// Velvet.g:165:1: groupType : ( SOMEOF | ONEOF );
	public final VelvetParser.groupType_return groupType() throws RecognitionException {
		final VelvetParser.groupType_return retval = new VelvetParser.groupType_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token set70 = null;

		final Tree set70_tree = null;

		try {
			// Velvet.g:166:2: ( SOMEOF | ONEOF )
			// Velvet.g:
			{
				root_0 = (Tree) adaptor.nil();

				set70 = input.LT(1);

				if ((input.LA(1) == ONEOF) || (input.LA(1) == SOMEOF)) {
					input.consume();
					adaptor.addChild(root_0, adaptor.create(set70));
					state.errorRecovery = false;
				} else {
					final MismatchedSetException mse = new MismatchedSetException(null, input);
					throw mse;
				}

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "groupType"

	public static class description_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "description"
	// Velvet.g:170:1: description : DESCRIPTION STRING SEMI -> ^( DESCRIPTION STRING ) ;
	public final VelvetParser.description_return description() throws RecognitionException {
		final VelvetParser.description_return retval = new VelvetParser.description_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token DESCRIPTION71 = null;
		Token STRING72 = null;
		Token SEMI73 = null;

		final Tree DESCRIPTION71_tree = null;
		final Tree STRING72_tree = null;
		final Tree SEMI73_tree = null;
		final RewriteRuleTokenStream stream_DESCRIPTION = new RewriteRuleTokenStream(adaptor, "token DESCRIPTION");
		final RewriteRuleTokenStream stream_SEMI = new RewriteRuleTokenStream(adaptor, "token SEMI");
		final RewriteRuleTokenStream stream_STRING = new RewriteRuleTokenStream(adaptor, "token STRING");

		try {
			// Velvet.g:171:2: ( DESCRIPTION STRING SEMI -> ^( DESCRIPTION STRING ) )
			// Velvet.g:171:4: DESCRIPTION STRING SEMI
			{
				DESCRIPTION71 = (Token) match(input, DESCRIPTION, FOLLOW_DESCRIPTION_in_description995);
				stream_DESCRIPTION.add(DESCRIPTION71);

				STRING72 = (Token) match(input, STRING, FOLLOW_STRING_in_description997);
				stream_STRING.add(STRING72);

				SEMI73 = (Token) match(input, SEMI, FOLLOW_SEMI_in_description999);
				stream_SEMI.add(SEMI73);

				// AST REWRITE
				// elements: STRING, DESCRIPTION
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 172:2: -> ^( DESCRIPTION STRING )
				{
					// Velvet.g:172:5: ^( DESCRIPTION STRING )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(stream_DESCRIPTION.nextNode(), root_1);

						adaptor.addChild(root_1, stream_STRING.nextNode());

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "description"

	public static class constraint_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "constraint"
	// Velvet.g:175:1: constraint : CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !;
	public final VelvetParser.constraint_return constraint() throws RecognitionException {
		final VelvetParser.constraint_return retval = new VelvetParser.constraint_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token CONSTRAINT74 = null;
		Token ID75 = null;
		Token EQ76 = null;
		Token SEMI79 = null;
		VelvetParser.constraintDefinition_return constraintDefinition77 = null;

		VelvetParser.attributeConstraint_return attributeConstraint78 = null;

		Tree CONSTRAINT74_tree = null;
		Tree ID75_tree = null;
		final Tree EQ76_tree = null;
		final Tree SEMI79_tree = null;

		try {
			// Velvet.g:176:2: ( CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !)
			// Velvet.g:176:4: CONSTRAINT ^ ( ID EQ !)? ( constraintDefinition | attributeConstraint ) SEMI !
			{
				root_0 = (Tree) adaptor.nil();

				CONSTRAINT74 = (Token) match(input, CONSTRAINT, FOLLOW_CONSTRAINT_in_constraint1020);
				CONSTRAINT74_tree = (Tree) adaptor.create(CONSTRAINT74);
				root_0 = (Tree) adaptor.becomeRoot(CONSTRAINT74_tree, root_0);

				// Velvet.g:176:16: ( ID EQ !)?
				int alt19 = 2;
				final int LA19_0 = input.LA(1);

				if ((LA19_0 == ID)) {
					final int LA19_1 = input.LA(2);

					if ((LA19_1 == EQ)) {
						alt19 = 1;
					}
				}
				switch (alt19) {
				case 1:
				// Velvet.g:176:17: ID EQ !
				{
					ID75 = (Token) match(input, ID, FOLLOW_ID_in_constraint1024);
					ID75_tree = (Tree) adaptor.create(ID75);
					adaptor.addChild(root_0, ID75_tree);

					EQ76 = (Token) match(input, EQ, FOLLOW_EQ_in_constraint1026);

				}
					break;

				}

				// Velvet.g:176:26: ( constraintDefinition | attributeConstraint )
				int alt20 = 2;
				switch (input.LA(1)) {
				case OP_NOT:
				case START_R: {
					alt20 = 1;
				}
					break;
				case ID:
				case IDPath: {
					final int LA20_2 = input.LA(2);

					if ((((LA20_2 >= OP_AND) && (LA20_2 <= OP_IMPLIES)) || ((LA20_2 >= OP_OR) && (LA20_2 <= OP_XOR)) || (LA20_2 == SEMI))) {
						alt20 = 1;
					} else if (((LA20_2 == ATTR_OP_EQUALS) || (LA20_2 == ATTR_OP_GREATER_EQ) || (LA20_2 == ATTR_OP_LESS_EQ) || (LA20_2 == MINUS)
						|| (LA20_2 == PLUS))) {
						alt20 = 2;
					} else {
						final NoViableAltException nvae = new NoViableAltException("", 20, 2, input);

						throw nvae;

					}
				}
					break;
				case INT: {
					alt20 = 2;
				}
					break;
				default:
					final NoViableAltException nvae = new NoViableAltException("", 20, 0, input);

					throw nvae;

				}

				switch (alt20) {
				case 1:
				// Velvet.g:176:27: constraintDefinition
				{
					pushFollow(FOLLOW_constraintDefinition_in_constraint1032);
					constraintDefinition77 = constraintDefinition();

					state._fsp--;

					adaptor.addChild(root_0, constraintDefinition77.getTree());

				}
					break;
				case 2:
				// Velvet.g:176:50: attributeConstraint
				{
					pushFollow(FOLLOW_attributeConstraint_in_constraint1036);
					attributeConstraint78 = attributeConstraint();

					state._fsp--;

					adaptor.addChild(root_0, attributeConstraint78.getTree());

				}
					break;

				}

				SEMI79 = (Token) match(input, SEMI, FOLLOW_SEMI_in_constraint1039);

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "constraint"

	public static class constraintDefinition_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "constraintDefinition"
	// Velvet.g:179:1: constraintDefinition : constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) ;
	public final VelvetParser.constraintDefinition_return constraintDefinition() throws RecognitionException {
		final VelvetParser.constraintDefinition_return retval = new VelvetParser.constraintDefinition_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		VelvetParser.constraintOperand_return constraintOperand80 = null;

		VelvetParser.binaryOp_return binaryOp81 = null;

		VelvetParser.constraintOperand_return constraintOperand82 = null;

		final RewriteRuleSubtreeStream stream_constraintOperand = new RewriteRuleSubtreeStream(adaptor, "rule constraintOperand");
		final RewriteRuleSubtreeStream stream_binaryOp = new RewriteRuleSubtreeStream(adaptor, "rule binaryOp");
		try {
			// Velvet.g:180:2: ( constraintOperand ( binaryOp constraintOperand )* -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* ) )
			// Velvet.g:180:4: constraintOperand ( binaryOp constraintOperand )*
			{
				pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1052);
				constraintOperand80 = constraintOperand();

				state._fsp--;

				stream_constraintOperand.add(constraintOperand80.getTree());

				// Velvet.g:180:22: ( binaryOp constraintOperand )*
				loop21: do {
					int alt21 = 2;
					final int LA21_0 = input.LA(1);

					if ((((LA21_0 >= OP_AND) && (LA21_0 <= OP_IMPLIES)) || ((LA21_0 >= OP_OR) && (LA21_0 <= OP_XOR)))) {
						alt21 = 1;
					}

					switch (alt21) {
					case 1:
					// Velvet.g:180:23: binaryOp constraintOperand
					{
						pushFollow(FOLLOW_binaryOp_in_constraintDefinition1055);
						binaryOp81 = binaryOp();

						state._fsp--;

						stream_binaryOp.add(binaryOp81.getTree());

						pushFollow(FOLLOW_constraintOperand_in_constraintDefinition1057);
						constraintOperand82 = constraintOperand();

						state._fsp--;

						stream_constraintOperand.add(constraintOperand82.getTree());

					}
						break;

					default:
						break loop21;
					}
				} while (true);

				// AST REWRITE
				// elements: constraintOperand, binaryOp
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 181:2: -> ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
				{
					// Velvet.g:181:5: ^( CONSTR ( constraintOperand )+ ( binaryOp )* )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(adaptor.create(CONSTR, "CONSTR"), root_1);

						if (!(stream_constraintOperand.hasNext())) {
							throw new RewriteEarlyExitException();
						}
						while (stream_constraintOperand.hasNext()) {
							adaptor.addChild(root_1, stream_constraintOperand.nextTree());

						}
						stream_constraintOperand.reset();

						// Velvet.g:181:33: ( binaryOp )*
						while (stream_binaryOp.hasNext()) {
							adaptor.addChild(root_1, stream_binaryOp.nextTree());

						}
						stream_binaryOp.reset();

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "constraintDefinition"

	public static class constraintOperand_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "constraintOperand"
	// Velvet.g:184:1: constraintOperand : ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* (
	// ^( OPERAND name ) )? ;
	public final VelvetParser.constraintOperand_return constraintOperand() throws RecognitionException {
		final VelvetParser.constraintOperand_return retval = new VelvetParser.constraintOperand_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token START_R84 = null;
		Token END_R86 = null;
		VelvetParser.unaryOp_return unaryOp83 = null;

		VelvetParser.constraintDefinition_return constraintDefinition85 = null;

		VelvetParser.name_return name87 = null;

		final Tree START_R84_tree = null;
		final Tree END_R86_tree = null;
		final RewriteRuleTokenStream stream_END_R = new RewriteRuleTokenStream(adaptor, "token END_R");
		final RewriteRuleTokenStream stream_START_R = new RewriteRuleTokenStream(adaptor, "token START_R");
		final RewriteRuleSubtreeStream stream_name = new RewriteRuleSubtreeStream(adaptor, "rule name");
		final RewriteRuleSubtreeStream stream_unaryOp = new RewriteRuleSubtreeStream(adaptor, "rule unaryOp");
		final RewriteRuleSubtreeStream stream_constraintDefinition = new RewriteRuleSubtreeStream(adaptor, "rule constraintDefinition");
		try {
			// Velvet.g:184:19: ( ( unaryOp )* ( START_R constraintDefinition END_R | name ) -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND
			// name ) )? )
			// Velvet.g:184:21: ( unaryOp )* ( START_R constraintDefinition END_R | name )
			{
				// Velvet.g:184:21: ( unaryOp )*
				loop22: do {
					int alt22 = 2;
					final int LA22_0 = input.LA(1);

					if ((LA22_0 == OP_NOT)) {
						alt22 = 1;
					}

					switch (alt22) {
					case 1:
					// Velvet.g:184:21: unaryOp
					{
						pushFollow(FOLLOW_unaryOp_in_constraintOperand1084);
						unaryOp83 = unaryOp();

						state._fsp--;

						stream_unaryOp.add(unaryOp83.getTree());

					}
						break;

					default:
						break loop22;
					}
				} while (true);

				// Velvet.g:184:30: ( START_R constraintDefinition END_R | name )
				int alt23 = 2;
				final int LA23_0 = input.LA(1);

				if ((LA23_0 == START_R)) {
					alt23 = 1;
				} else if ((((LA23_0 >= ID) && (LA23_0 <= IDPath)))) {
					alt23 = 2;
				} else {
					final NoViableAltException nvae = new NoViableAltException("", 23, 0, input);

					throw nvae;

				}
				switch (alt23) {
				case 1:
				// Velvet.g:184:31: START_R constraintDefinition END_R
				{
					START_R84 = (Token) match(input, START_R, FOLLOW_START_R_in_constraintOperand1088);
					stream_START_R.add(START_R84);

					pushFollow(FOLLOW_constraintDefinition_in_constraintOperand1090);
					constraintDefinition85 = constraintDefinition();

					state._fsp--;

					stream_constraintDefinition.add(constraintDefinition85.getTree());

					END_R86 = (Token) match(input, END_R, FOLLOW_END_R_in_constraintOperand1092);
					stream_END_R.add(END_R86);

				}
					break;
				case 2:
				// Velvet.g:184:68: name
				{
					pushFollow(FOLLOW_name_in_constraintOperand1096);
					name87 = name();

					state._fsp--;

					stream_name.add(name87.getTree());

				}
					break;

				}

				// AST REWRITE
				// elements: name, constraintDefinition, unaryOp
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 185:2: -> ( constraintDefinition )? ( ^( UNARYOP unaryOp ) )* ( ^( OPERAND name ) )?
				{
					// Velvet.g:185:5: ( constraintDefinition )?
					if (stream_constraintDefinition.hasNext()) {
						adaptor.addChild(root_0, stream_constraintDefinition.nextTree());

					}
					stream_constraintDefinition.reset();

					// Velvet.g:185:27: ( ^( UNARYOP unaryOp ) )*
					while (stream_unaryOp.hasNext()) {
						// Velvet.g:185:27: ^( UNARYOP unaryOp )
						{
							Tree root_1 = (Tree) adaptor.nil();
							root_1 = (Tree) adaptor.becomeRoot(adaptor.create(UNARYOP, "UNARYOP"), root_1);

							adaptor.addChild(root_1, stream_unaryOp.nextTree());

							adaptor.addChild(root_0, root_1);
						}

					}
					stream_unaryOp.reset();

					// Velvet.g:185:47: ( ^( OPERAND name ) )?
					if (stream_name.hasNext()) {
						// Velvet.g:185:47: ^( OPERAND name )
						{
							Tree root_1 = (Tree) adaptor.nil();
							root_1 = (Tree) adaptor.becomeRoot(adaptor.create(OPERAND, "OPERAND"), root_1);

							adaptor.addChild(root_1, stream_name.nextTree());

							adaptor.addChild(root_0, root_1);
						}

					}
					stream_name.reset();

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "constraintOperand"

	public static class attribute_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "attribute"
	// Velvet.g:188:1: attribute : ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? (
	// stringAttribute )? ( boolAttribute )? ) ;
	public final VelvetParser.attribute_return attribute() throws RecognitionException {
		final VelvetParser.attribute_return retval = new VelvetParser.attribute_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token SEMI92 = null;
		VelvetParser.intAttribute_return intAttribute88 = null;

		VelvetParser.floatAttribute_return floatAttribute89 = null;

		VelvetParser.stringAttribute_return stringAttribute90 = null;

		VelvetParser.boolAttribute_return boolAttribute91 = null;

		final Tree SEMI92_tree = null;
		final RewriteRuleTokenStream stream_SEMI = new RewriteRuleTokenStream(adaptor, "token SEMI");
		final RewriteRuleSubtreeStream stream_intAttribute = new RewriteRuleSubtreeStream(adaptor, "rule intAttribute");
		final RewriteRuleSubtreeStream stream_stringAttribute = new RewriteRuleSubtreeStream(adaptor, "rule stringAttribute");
		final RewriteRuleSubtreeStream stream_floatAttribute = new RewriteRuleSubtreeStream(adaptor, "rule floatAttribute");
		final RewriteRuleSubtreeStream stream_boolAttribute = new RewriteRuleSubtreeStream(adaptor, "rule boolAttribute");
		try {
			// Velvet.g:189:2: ( ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI -> ^( ATTR ( intAttribute )? ( floatAttribute )? (
			// stringAttribute )? ( boolAttribute )? ) )
			// Velvet.g:189:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute ) SEMI
			{
				// Velvet.g:189:4: ( intAttribute | floatAttribute | stringAttribute | boolAttribute )
				int alt24 = 4;
				switch (input.LA(1)) {
				case VAR_INT: {
					alt24 = 1;
				}
					break;
				case VAR_FLOAT: {
					alt24 = 2;
				}
					break;
				case VAR_STRING: {
					alt24 = 3;
				}
					break;
				case VAR_BOOL: {
					alt24 = 4;
				}
					break;
				default:
					final NoViableAltException nvae = new NoViableAltException("", 24, 0, input);

					throw nvae;

				}

				switch (alt24) {
				case 1:
				// Velvet.g:189:5: intAttribute
				{
					pushFollow(FOLLOW_intAttribute_in_attribute1132);
					intAttribute88 = intAttribute();

					state._fsp--;

					stream_intAttribute.add(intAttribute88.getTree());

				}
					break;
				case 2:
				// Velvet.g:189:20: floatAttribute
				{
					pushFollow(FOLLOW_floatAttribute_in_attribute1136);
					floatAttribute89 = floatAttribute();

					state._fsp--;

					stream_floatAttribute.add(floatAttribute89.getTree());

				}
					break;
				case 3:
				// Velvet.g:189:37: stringAttribute
				{
					pushFollow(FOLLOW_stringAttribute_in_attribute1140);
					stringAttribute90 = stringAttribute();

					state._fsp--;

					stream_stringAttribute.add(stringAttribute90.getTree());

				}
					break;
				case 4:
				// Velvet.g:189:55: boolAttribute
				{
					pushFollow(FOLLOW_boolAttribute_in_attribute1144);
					boolAttribute91 = boolAttribute();

					state._fsp--;

					stream_boolAttribute.add(boolAttribute91.getTree());

				}
					break;

				}

				SEMI92 = (Token) match(input, SEMI, FOLLOW_SEMI_in_attribute1147);
				stream_SEMI.add(SEMI92);

				// AST REWRITE
				// elements: stringAttribute, floatAttribute, intAttribute, boolAttribute
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 190:2: -> ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
				{
					// Velvet.g:190:5: ^( ATTR ( intAttribute )? ( floatAttribute )? ( stringAttribute )? ( boolAttribute )? )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(adaptor.create(ATTR, "ATTR"), root_1);

						// Velvet.g:190:12: ( intAttribute )?
						if (stream_intAttribute.hasNext()) {
							adaptor.addChild(root_1, stream_intAttribute.nextTree());

						}
						stream_intAttribute.reset();

						// Velvet.g:190:26: ( floatAttribute )?
						if (stream_floatAttribute.hasNext()) {
							adaptor.addChild(root_1, stream_floatAttribute.nextTree());

						}
						stream_floatAttribute.reset();

						// Velvet.g:190:42: ( stringAttribute )?
						if (stream_stringAttribute.hasNext()) {
							adaptor.addChild(root_1, stream_stringAttribute.nextTree());

						}
						stream_stringAttribute.reset();

						// Velvet.g:190:59: ( boolAttribute )?
						if (stream_boolAttribute.hasNext()) {
							adaptor.addChild(root_1, stream_boolAttribute.nextTree());

						}
						stream_boolAttribute.reset();

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "attribute"

	public static class attributeConstraint_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "attributeConstraint"
	// Velvet.g:193:1: attributeConstraint : attribConstraint -> ^( ACONSTR attribConstraint ) ;
	public final VelvetParser.attributeConstraint_return attributeConstraint() throws RecognitionException {
		final VelvetParser.attributeConstraint_return retval = new VelvetParser.attributeConstraint_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		VelvetParser.attribConstraint_return attribConstraint93 = null;

		final RewriteRuleSubtreeStream stream_attribConstraint = new RewriteRuleSubtreeStream(adaptor, "rule attribConstraint");
		try {
			// Velvet.g:194:2: ( attribConstraint -> ^( ACONSTR attribConstraint ) )
			// Velvet.g:194:4: attribConstraint
			{
				pushFollow(FOLLOW_attribConstraint_in_attributeConstraint1178);
				attribConstraint93 = attribConstraint();

				state._fsp--;

				stream_attribConstraint.add(attribConstraint93.getTree());

				// AST REWRITE
				// elements: attribConstraint
				// token labels:
				// rule labels: retval
				// token list labels:
				// rule list labels:
				// wildcard labels:
				retval.tree = root_0;
				final RewriteRuleSubtreeStream stream_retval = new RewriteRuleSubtreeStream(adaptor, "rule retval", retval != null ? retval.tree : null);

				root_0 = (Tree) adaptor.nil();
				// 195:2: -> ^( ACONSTR attribConstraint )
				{
					// Velvet.g:195:5: ^( ACONSTR attribConstraint )
					{
						Tree root_1 = (Tree) adaptor.nil();
						root_1 = (Tree) adaptor.becomeRoot(adaptor.create(ACONSTR, "ACONSTR"), root_1);

						adaptor.addChild(root_1, stream_attribConstraint.nextTree());

						adaptor.addChild(root_0, root_1);
					}

				}

				retval.tree = root_0;

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "attributeConstraint"

	public static class attribConstraint_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "attribConstraint"
	// Velvet.g:198:1: attribConstraint : attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator
	// attribNumInstance )* ;
	public final VelvetParser.attribConstraint_return attribConstraint() throws RecognitionException {
		final VelvetParser.attribConstraint_return retval = new VelvetParser.attribConstraint_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		VelvetParser.attribNumInstance_return attribNumInstance94 = null;

		VelvetParser.attribOperator_return attribOperator95 = null;

		VelvetParser.attribNumInstance_return attribNumInstance96 = null;

		VelvetParser.attribRelation_return attribRelation97 = null;

		VelvetParser.attribNumInstance_return attribNumInstance98 = null;

		VelvetParser.attribOperator_return attribOperator99 = null;

		VelvetParser.attribNumInstance_return attribNumInstance100 = null;

		try {
			// Velvet.g:199:2: ( attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )*
			// )
			// Velvet.g:199:4: attribNumInstance ( attribOperator attribNumInstance )* attribRelation attribNumInstance ( attribOperator attribNumInstance )*
			{
				root_0 = (Tree) adaptor.nil();

				pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1198);
				attribNumInstance94 = attribNumInstance();

				state._fsp--;

				adaptor.addChild(root_0, attribNumInstance94.getTree());

				// Velvet.g:199:22: ( attribOperator attribNumInstance )*
				loop25: do {
					int alt25 = 2;
					final int LA25_0 = input.LA(1);

					if (((LA25_0 == MINUS) || (LA25_0 == PLUS))) {
						alt25 = 1;
					}

					switch (alt25) {
					case 1:
					// Velvet.g:199:23: attribOperator attribNumInstance
					{
						pushFollow(FOLLOW_attribOperator_in_attribConstraint1201);
						attribOperator95 = attribOperator();

						state._fsp--;

						adaptor.addChild(root_0, attribOperator95.getTree());

						pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1203);
						attribNumInstance96 = attribNumInstance();

						state._fsp--;

						adaptor.addChild(root_0, attribNumInstance96.getTree());

					}
						break;

					default:
						break loop25;
					}
				} while (true);

				pushFollow(FOLLOW_attribRelation_in_attribConstraint1211);
				attribRelation97 = attribRelation();

				state._fsp--;

				adaptor.addChild(root_0, attribRelation97.getTree());

				pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1217);
				attribNumInstance98 = attribNumInstance();

				state._fsp--;

				adaptor.addChild(root_0, attribNumInstance98.getTree());

				// Velvet.g:201:22: ( attribOperator attribNumInstance )*
				loop26: do {
					int alt26 = 2;
					final int LA26_0 = input.LA(1);

					if (((LA26_0 == MINUS) || (LA26_0 == PLUS))) {
						alt26 = 1;
					}

					switch (alt26) {
					case 1:
					// Velvet.g:201:23: attribOperator attribNumInstance
					{
						pushFollow(FOLLOW_attribOperator_in_attribConstraint1220);
						attribOperator99 = attribOperator();

						state._fsp--;

						adaptor.addChild(root_0, attribOperator99.getTree());

						pushFollow(FOLLOW_attribNumInstance_in_attribConstraint1222);
						attribNumInstance100 = attribNumInstance();

						state._fsp--;

						adaptor.addChild(root_0, attribNumInstance100.getTree());

					}
						break;

					default:
						break loop26;
					}
				} while (true);

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "attribConstraint"

	public static class attribOperator_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "attribOperator"
	// Velvet.g:204:1: attribOperator : ( PLUS | MINUS );
	public final VelvetParser.attribOperator_return attribOperator() throws RecognitionException {
		final VelvetParser.attribOperator_return retval = new VelvetParser.attribOperator_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token set101 = null;

		final Tree set101_tree = null;

		try {
			// Velvet.g:205:2: ( PLUS | MINUS )
			// Velvet.g:
			{
				root_0 = (Tree) adaptor.nil();

				set101 = input.LT(1);

				if ((input.LA(1) == MINUS) || (input.LA(1) == PLUS)) {
					input.consume();
					adaptor.addChild(root_0, adaptor.create(set101));
					state.errorRecovery = false;
				} else {
					final MismatchedSetException mse = new MismatchedSetException(null, input);
					throw mse;
				}

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "attribOperator"

	public static class attribNumInstance_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "attribNumInstance"
	// Velvet.g:209:1: attribNumInstance : ( INT | name );
	public final VelvetParser.attribNumInstance_return attribNumInstance() throws RecognitionException {
		final VelvetParser.attribNumInstance_return retval = new VelvetParser.attribNumInstance_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token INT102 = null;
		VelvetParser.name_return name103 = null;

		Tree INT102_tree = null;

		try {
			// Velvet.g:210:2: ( INT | name )
			int alt27 = 2;
			final int LA27_0 = input.LA(1);

			if ((LA27_0 == INT)) {
				alt27 = 1;
			} else if ((((LA27_0 >= ID) && (LA27_0 <= IDPath)))) {
				alt27 = 2;
			} else {
				final NoViableAltException nvae = new NoViableAltException("", 27, 0, input);

				throw nvae;

			}
			switch (alt27) {
			case 1:
			// Velvet.g:210:4: INT
			{
				root_0 = (Tree) adaptor.nil();

				INT102 = (Token) match(input, INT, FOLLOW_INT_in_attribNumInstance1254);
				INT102_tree = (Tree) adaptor.create(INT102);
				adaptor.addChild(root_0, INT102_tree);

			}
				break;
			case 2:
			// Velvet.g:212:4: name
			{
				root_0 = (Tree) adaptor.nil();

				pushFollow(FOLLOW_name_in_attribNumInstance1261);
				name103 = name();

				state._fsp--;

				adaptor.addChild(root_0, name103.getTree());

			}
				break;

			}
			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "attribNumInstance"

	public static class intAttribute_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "intAttribute"
	// Velvet.g:215:1: intAttribute : VAR_INT ! name ( EQ ! INT )? ;
	public final VelvetParser.intAttribute_return intAttribute() throws RecognitionException {
		final VelvetParser.intAttribute_return retval = new VelvetParser.intAttribute_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token VAR_INT104 = null;
		Token EQ106 = null;
		Token INT107 = null;
		VelvetParser.name_return name105 = null;

		final Tree VAR_INT104_tree = null;
		final Tree EQ106_tree = null;
		Tree INT107_tree = null;

		try {
			// Velvet.g:215:13: ( VAR_INT ! name ( EQ ! INT )? )
			// Velvet.g:215:16: VAR_INT ! name ( EQ ! INT )?
			{
				root_0 = (Tree) adaptor.nil();

				VAR_INT104 = (Token) match(input, VAR_INT, FOLLOW_VAR_INT_in_intAttribute1271);

				pushFollow(FOLLOW_name_in_intAttribute1274);
				name105 = name();

				state._fsp--;

				adaptor.addChild(root_0, name105.getTree());

				// Velvet.g:215:30: ( EQ ! INT )?
				int alt28 = 2;
				final int LA28_0 = input.LA(1);

				if ((LA28_0 == EQ)) {
					alt28 = 1;
				}
				switch (alt28) {
				case 1:
				// Velvet.g:215:31: EQ ! INT
				{
					EQ106 = (Token) match(input, EQ, FOLLOW_EQ_in_intAttribute1277);

					INT107 = (Token) match(input, INT, FOLLOW_INT_in_intAttribute1280);
					INT107_tree = (Tree) adaptor.create(INT107);
					adaptor.addChild(root_0, INT107_tree);

				}
					break;

				}

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "intAttribute"

	public static class floatAttribute_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "floatAttribute"
	// Velvet.g:216:1: floatAttribute : VAR_FLOAT ! name ( EQ ! FLOAT )? ;
	public final VelvetParser.floatAttribute_return floatAttribute() throws RecognitionException {
		final VelvetParser.floatAttribute_return retval = new VelvetParser.floatAttribute_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token VAR_FLOAT108 = null;
		Token EQ110 = null;
		Token FLOAT111 = null;
		VelvetParser.name_return name109 = null;

		final Tree VAR_FLOAT108_tree = null;
		final Tree EQ110_tree = null;
		Tree FLOAT111_tree = null;

		try {
			// Velvet.g:216:15: ( VAR_FLOAT ! name ( EQ ! FLOAT )? )
			// Velvet.g:216:18: VAR_FLOAT ! name ( EQ ! FLOAT )?
			{
				root_0 = (Tree) adaptor.nil();

				VAR_FLOAT108 = (Token) match(input, VAR_FLOAT, FOLLOW_VAR_FLOAT_in_floatAttribute1289);

				pushFollow(FOLLOW_name_in_floatAttribute1292);
				name109 = name();

				state._fsp--;

				adaptor.addChild(root_0, name109.getTree());

				// Velvet.g:216:34: ( EQ ! FLOAT )?
				int alt29 = 2;
				final int LA29_0 = input.LA(1);

				if ((LA29_0 == EQ)) {
					alt29 = 1;
				}
				switch (alt29) {
				case 1:
				// Velvet.g:216:35: EQ ! FLOAT
				{
					EQ110 = (Token) match(input, EQ, FOLLOW_EQ_in_floatAttribute1295);

					FLOAT111 = (Token) match(input, FLOAT, FOLLOW_FLOAT_in_floatAttribute1298);
					FLOAT111_tree = (Tree) adaptor.create(FLOAT111);
					adaptor.addChild(root_0, FLOAT111_tree);

				}
					break;

				}

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "floatAttribute"

	public static class stringAttribute_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "stringAttribute"
	// Velvet.g:217:1: stringAttribute : VAR_STRING ! name ( EQ ! STRING )? ;
	public final VelvetParser.stringAttribute_return stringAttribute() throws RecognitionException {
		final VelvetParser.stringAttribute_return retval = new VelvetParser.stringAttribute_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token VAR_STRING112 = null;
		Token EQ114 = null;
		Token STRING115 = null;
		VelvetParser.name_return name113 = null;

		final Tree VAR_STRING112_tree = null;
		final Tree EQ114_tree = null;
		Tree STRING115_tree = null;

		try {
			// Velvet.g:217:16: ( VAR_STRING ! name ( EQ ! STRING )? )
			// Velvet.g:217:18: VAR_STRING ! name ( EQ ! STRING )?
			{
				root_0 = (Tree) adaptor.nil();

				VAR_STRING112 = (Token) match(input, VAR_STRING, FOLLOW_VAR_STRING_in_stringAttribute1306);

				pushFollow(FOLLOW_name_in_stringAttribute1309);
				name113 = name();

				state._fsp--;

				adaptor.addChild(root_0, name113.getTree());

				// Velvet.g:217:35: ( EQ ! STRING )?
				int alt30 = 2;
				final int LA30_0 = input.LA(1);

				if ((LA30_0 == EQ)) {
					alt30 = 1;
				}
				switch (alt30) {
				case 1:
				// Velvet.g:217:36: EQ ! STRING
				{
					EQ114 = (Token) match(input, EQ, FOLLOW_EQ_in_stringAttribute1312);

					STRING115 = (Token) match(input, STRING, FOLLOW_STRING_in_stringAttribute1315);
					STRING115_tree = (Tree) adaptor.create(STRING115);
					adaptor.addChild(root_0, STRING115_tree);

				}
					break;

				}

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "stringAttribute"

	public static class boolAttribute_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "boolAttribute"
	// Velvet.g:218:1: boolAttribute : VAR_BOOL ! name ( EQ ! BOOLEAN )? ;
	public final VelvetParser.boolAttribute_return boolAttribute() throws RecognitionException {
		final VelvetParser.boolAttribute_return retval = new VelvetParser.boolAttribute_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token VAR_BOOL116 = null;
		Token EQ118 = null;
		Token BOOLEAN119 = null;
		VelvetParser.name_return name117 = null;

		final Tree VAR_BOOL116_tree = null;
		final Tree EQ118_tree = null;
		Tree BOOLEAN119_tree = null;

		try {
			// Velvet.g:218:14: ( VAR_BOOL ! name ( EQ ! BOOLEAN )? )
			// Velvet.g:218:17: VAR_BOOL ! name ( EQ ! BOOLEAN )?
			{
				root_0 = (Tree) adaptor.nil();

				VAR_BOOL116 = (Token) match(input, VAR_BOOL, FOLLOW_VAR_BOOL_in_boolAttribute1324);

				pushFollow(FOLLOW_name_in_boolAttribute1327);
				name117 = name();

				state._fsp--;

				adaptor.addChild(root_0, name117.getTree());

				// Velvet.g:218:32: ( EQ ! BOOLEAN )?
				int alt31 = 2;
				final int LA31_0 = input.LA(1);

				if ((LA31_0 == EQ)) {
					alt31 = 1;
				}
				switch (alt31) {
				case 1:
				// Velvet.g:218:33: EQ ! BOOLEAN
				{
					EQ118 = (Token) match(input, EQ, FOLLOW_EQ_in_boolAttribute1330);

					BOOLEAN119 = (Token) match(input, BOOLEAN, FOLLOW_BOOLEAN_in_boolAttribute1333);
					BOOLEAN119_tree = (Tree) adaptor.create(BOOLEAN119);
					adaptor.addChild(root_0, BOOLEAN119_tree);

				}
					break;

				}

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "boolAttribute"

	public static class unaryOp_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "unaryOp"
	// Velvet.g:220:1: unaryOp : OP_NOT ;
	public final VelvetParser.unaryOp_return unaryOp() throws RecognitionException {
		final VelvetParser.unaryOp_return retval = new VelvetParser.unaryOp_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token OP_NOT120 = null;

		Tree OP_NOT120_tree = null;

		try {
			// Velvet.g:221:2: ( OP_NOT )
			// Velvet.g:221:4: OP_NOT
			{
				root_0 = (Tree) adaptor.nil();

				OP_NOT120 = (Token) match(input, OP_NOT, FOLLOW_OP_NOT_in_unaryOp1345);
				OP_NOT120_tree = (Tree) adaptor.create(OP_NOT120);
				adaptor.addChild(root_0, OP_NOT120_tree);

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "unaryOp"

	public static class binaryOp_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "binaryOp"
	// Velvet.g:224:1: binaryOp : ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT );
	public final VelvetParser.binaryOp_return binaryOp() throws RecognitionException {
		final VelvetParser.binaryOp_return retval = new VelvetParser.binaryOp_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token set121 = null;

		final Tree set121_tree = null;

		try {
			// Velvet.g:225:2: ( OP_AND | OP_OR | OP_XOR | OP_IMPLIES | OP_EQUIVALENT )
			// Velvet.g:
			{
				root_0 = (Tree) adaptor.nil();

				set121 = input.LT(1);

				if (((input.LA(1) >= OP_AND) && (input.LA(1) <= OP_IMPLIES)) || ((input.LA(1) >= OP_OR) && (input.LA(1) <= OP_XOR))) {
					input.consume();
					adaptor.addChild(root_0, adaptor.create(set121));
					state.errorRecovery = false;
				} else {
					final MismatchedSetException mse = new MismatchedSetException(null, input);
					throw mse;
				}

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "binaryOp"

	public static class attribRelation_return extends ParserRuleReturnScope {

		Tree tree;

		@Override
		public Object getTree() {
			return tree;
		}
	};

	// $ANTLR start "attribRelation"
	// Velvet.g:232:1: attribRelation : ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ );
	public final VelvetParser.attribRelation_return attribRelation() throws RecognitionException {
		final VelvetParser.attribRelation_return retval = new VelvetParser.attribRelation_return();
		retval.start = input.LT(1);

		Tree root_0 = null;

		Token set122 = null;

		final Tree set122_tree = null;

		try {
			// Velvet.g:233:2: ( ATTR_OP_EQUALS | ATTR_OP_GREATER_EQ | ATTR_OP_LESS_EQ )
			// Velvet.g:
			{
				root_0 = (Tree) adaptor.nil();

				set122 = input.LT(1);

				if ((input.LA(1) == ATTR_OP_EQUALS) || (input.LA(1) == ATTR_OP_GREATER_EQ) || (input.LA(1) == ATTR_OP_LESS_EQ)) {
					input.consume();
					adaptor.addChild(root_0, adaptor.create(set122));
					state.errorRecovery = false;
				} else {
					final MismatchedSetException mse = new MismatchedSetException(null, input);
					throw mse;
				}

			}

			retval.stop = input.LT(-1);

			retval.tree = (Tree) adaptor.rulePostProcessing(root_0);
			adaptor.setTokenBoundaries(retval.tree, retval.start, retval.stop);

		} catch (final RecognitionException re) {
			reportError(re);
			recover(input, re);
			retval.tree = (Tree) adaptor.errorNode(input, retval.start, input.LT(-1), re);

		}

		finally {
			// do for sure before leaving
		}
		return retval;
	}
	// $ANTLR end "attribRelation"

	// Delegated rules

	protected DFA5 dfa5 = new DFA5(this);
	static final String DFA5_eotS = "\22\uffff";
	static final String DFA5_eofS = "\1\3\5\uffff\1\12\1\15\10\uffff\1\12\1\15";
	static final String DFA5_minS = "\1\44\2\41\1\uffff\2\41\2\21\1\41\2\uffff\1\41\2\uffff\2\41\2\21";
	static final String DFA5_maxS = "\1\67\2\41\1\uffff\2\42\2\67\1\41\2\uffff\1\41\2\uffff\2\42\2\67";
	static final String DFA5_acceptS = "\3\uffff\1\5\5\uffff\1\1\1\4\1\uffff\1\2\1\3\4\uffff";
	static final String DFA5_specialS = "\22\uffff}>";
	static final String[] DFA5_transitionS =
		{ "\1\1\1\2\21\uffff\1\3", "\1\4", "\1\5", "", "\2\6", "\2\7", "\1\10\23\uffff\1\11\21\uffff\1\12", "\1\13\22\uffff\1\14\22\uffff\1\15", "\1\16", "",
			"", "\1\17", "", "", "\2\20", "\2\21", "\1\10\23\uffff\1\11\21\uffff\1\12", "\1\13\22\uffff\1\14\22\uffff\1\15" };

	static final short[] DFA5_eot = DFA.unpackEncodedString(DFA5_eotS);
	static final short[] DFA5_eof = DFA.unpackEncodedString(DFA5_eofS);
	static final char[] DFA5_min = DFA.unpackEncodedStringToUnsignedChars(DFA5_minS);
	static final char[] DFA5_max = DFA.unpackEncodedStringToUnsignedChars(DFA5_maxS);
	static final short[] DFA5_accept = DFA.unpackEncodedString(DFA5_acceptS);
	static final short[] DFA5_special = DFA.unpackEncodedString(DFA5_specialS);
	static final short[][] DFA5_transition;

	static {
		final int numStates = DFA5_transitionS.length;
		DFA5_transition = new short[numStates][];
		for (int i = 0; i < numStates; i++) {
			DFA5_transition[i] = DFA.unpackEncodedString(DFA5_transitionS[i]);
		}
	}

	class DFA5 extends DFA {

		public DFA5(BaseRecognizer recognizer) {
			this.recognizer = recognizer;
			decisionNumber = 5;
			eot = DFA5_eot;
			eof = DFA5_eof;
			min = DFA5_min;
			max = DFA5_max;
			accept = DFA5_accept;
			special = DFA5_special;
			transition = DFA5_transition;
		}

		@Override
		public String getDescription() {
			return "104:27: ( instanceImports interfaceImports | interfaceImports instanceImports | interfaceImports | instanceImports )?";
		}
	}

	public static final BitSet FOLLOW_imp_in_velvetModel472 = new BitSet(new long[] { 0x0000000000048000L });
	public static final BitSet FOLLOW_concept_in_velvetModel476 = new BitSet(new long[] { 0x0000000000000000L });
	public static final BitSet FOLLOW_cinterface_in_velvetModel478 = new BitSet(new long[] { 0x0000000000000000L });
	public static final BitSet FOLLOW_EOF_in_velvetModel481 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_IMPORT_in_imp493 = new BitSet(new long[] { 0x0000000600000000L });
	public static final BitSet FOLLOW_name_in_imp495 = new BitSet(new long[] { 0x0010000000000000L });
	public static final BitSet FOLLOW_SEMI_in_imp497 = new BitSet(new long[] { 0x0000000800000002L });
	public static final BitSet FOLLOW_CONCEPT_in_concept521 = new BitSet(new long[] { 0x0000000200000000L });
	public static final BitSet FOLLOW_ID_in_concept523 = new BitSet(new long[] { 0x0080003000010002L });
	public static final BitSet FOLLOW_COLON_in_concept530 = new BitSet(new long[] { 0x0000000200000000L });
	public static final BitSet FOLLOW_conceptBaseExt_in_concept532 = new BitSet(new long[] { 0x0080003000000002L });
	public static final BitSet FOLLOW_instanceImports_in_concept537 = new BitSet(new long[] { 0x0000002000000000L });
	public static final BitSet FOLLOW_interfaceImports_in_concept539 = new BitSet(new long[] { 0x0080000000000002L });
	public static final BitSet FOLLOW_interfaceImports_in_concept543 = new BitSet(new long[] { 0x0000001000000000L });
	public static final BitSet FOLLOW_instanceImports_in_concept545 = new BitSet(new long[] { 0x0080000000000002L });
	public static final BitSet FOLLOW_interfaceImports_in_concept549 = new BitSet(new long[] { 0x0080000000000002L });
	public static final BitSet FOLLOW_instanceImports_in_concept553 = new BitSet(new long[] { 0x0080000000000002L });
	public static final BitSet FOLLOW_definitions_in_concept560 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_CINTERFACE_in_cinterface593 = new BitSet(new long[] { 0x0000000200000000L });
	public static final BitSet FOLLOW_ID_in_cinterface595 = new BitSet(new long[] { 0x0080000000010000L });
	public static final BitSet FOLLOW_COLON_in_cinterface599 = new BitSet(new long[] { 0x0000000200000000L });
	public static final BitSet FOLLOW_conceptBaseExt_in_cinterface601 = new BitSet(new long[] { 0x0080000000000000L });
	public static final BitSet FOLLOW_definitions_in_cinterface605 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_ID_in_conceptBaseExt632 = new BitSet(new long[] { 0x0000000000020002L });
	public static final BitSet FOLLOW_COMMA_in_conceptBaseExt635 = new BitSet(new long[] { 0x0000000200000000L });
	public static final BitSet FOLLOW_ID_in_conceptBaseExt637 = new BitSet(new long[] { 0x0000000000020002L });
	public static final BitSet FOLLOW_IMPORTINSTANCE_in_instanceImports662 = new BitSet(new long[] { 0x0000000200000000L });
	public static final BitSet FOLLOW_ID_in_instanceImports664 = new BitSet(new long[] { 0x0000000600000000L });
	public static final BitSet FOLLOW_name_in_instanceImports666 = new BitSet(new long[] { 0x0000000000020002L });
	public static final BitSet FOLLOW_COMMA_in_instanceImports669 = new BitSet(new long[] { 0x0000000200000000L });
	public static final BitSet FOLLOW_ID_in_instanceImports671 = new BitSet(new long[] { 0x0000000600000000L });
	public static final BitSet FOLLOW_name_in_instanceImports673 = new BitSet(new long[] { 0x0000000000020002L });
	public static final BitSet FOLLOW_IMPORTINTERFACE_in_interfaceImports702 = new BitSet(new long[] { 0x0000000200000000L });
	public static final BitSet FOLLOW_ID_in_interfaceImports704 = new BitSet(new long[] { 0x0000000600000000L });
	public static final BitSet FOLLOW_name_in_interfaceImports706 = new BitSet(new long[] { 0x0000000000020002L });
	public static final BitSet FOLLOW_COMMA_in_interfaceImports709 = new BitSet(new long[] { 0x0000000200000000L });
	public static final BitSet FOLLOW_ID_in_interfaceImports711 = new BitSet(new long[] { 0x0000000600000000L });
	public static final BitSet FOLLOW_name_in_interfaceImports713 = new BitSet(new long[] { 0x0000000000020002L });
	public static final BitSet FOLLOW_START_C_in_definitions757 = new BitSet(new long[] { 0xF040088021500010L, 0x0000000000000001L });
	public static final BitSet FOLLOW_definition_in_definitions759 = new BitSet(new long[] { 0x0000000001000000L });
	public static final BitSet FOLLOW_END_C_in_definitions761 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_nonFeatureDefinition_in_definition785 = new BitSet(new long[] { 0xF040088020500012L, 0x0000000000000001L });
	public static final BitSet FOLLOW_featureGroup_in_definition793 = new BitSet(new long[] { 0xF000000000500002L, 0x0000000000000001L });
	public static final BitSet FOLLOW_nonFeatureDefinition_in_definition795 = new BitSet(new long[] { 0xF000000000500002L, 0x0000000000000001L });
	public static final BitSet FOLLOW_feature_in_definition802 = new BitSet(new long[] { 0xF000008020500012L, 0x0000000000000001L });
	public static final BitSet FOLLOW_feature_in_definition805 = new BitSet(new long[] { 0xF000008020500012L, 0x0000000000000001L });
	public static final BitSet FOLLOW_nonFeatureDefinition_in_definition809 = new BitSet(new long[] { 0xF000008020500012L, 0x0000000000000001L });
	public static final BitSet FOLLOW_constraint_in_nonFeatureDefinition831 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_use_in_nonFeatureDefinition836 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_attribute_in_nonFeatureDefinition841 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_description_in_nonFeatureDefinition847 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_USE_in_use858 = new BitSet(new long[] { 0x0000000600000000L });
	public static final BitSet FOLLOW_name_in_use860 = new BitSet(new long[] { 0x0010000000000000L });
	public static final BitSet FOLLOW_SEMI_in_use862 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_MANDATORY_in_feature883 = new BitSet(new long[] { 0x0000000000000010L });
	public static final BitSet FOLLOW_ABSTRACT_in_feature885 = new BitSet(new long[] { 0x0000000020000000L });
	public static final BitSet FOLLOW_ABSTRACT_in_feature889 = new BitSet(new long[] { 0x0000008000000000L });
	public static final BitSet FOLLOW_MANDATORY_in_feature891 = new BitSet(new long[] { 0x0000000020000000L });
	public static final BitSet FOLLOW_MANDATORY_in_feature895 = new BitSet(new long[] { 0x0000000020000000L });
	public static final BitSet FOLLOW_ABSTRACT_in_feature899 = new BitSet(new long[] { 0x0000000020000000L });
	public static final BitSet FOLLOW_FEATURE_in_feature906 = new BitSet(new long[] { 0x0000000600000000L });
	public static final BitSet FOLLOW_name_in_feature908 = new BitSet(new long[] { 0x0090000000000000L });
	public static final BitSet FOLLOW_definitions_in_feature911 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_SEMI_in_feature915 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_groupType_in_featureGroup946 = new BitSet(new long[] { 0x0080000000000000L });
	public static final BitSet FOLLOW_START_C_in_featureGroup948 = new BitSet(new long[] { 0x0000008020000010L });
	public static final BitSet FOLLOW_feature_in_featureGroup950 = new BitSet(new long[] { 0x0000008021000010L });
	public static final BitSet FOLLOW_END_C_in_featureGroup953 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_DESCRIPTION_in_description995 = new BitSet(new long[] { 0x0200000000000000L });
	public static final BitSet FOLLOW_STRING_in_description997 = new BitSet(new long[] { 0x0010000000000000L });
	public static final BitSet FOLLOW_SEMI_in_description999 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_CONSTRAINT_in_constraint1020 = new BitSet(new long[] { 0x0101004600000000L });
	public static final BitSet FOLLOW_ID_in_constraint1024 = new BitSet(new long[] { 0x0000000004000000L });
	public static final BitSet FOLLOW_EQ_in_constraint1026 = new BitSet(new long[] { 0x0101004600000000L });
	public static final BitSet FOLLOW_constraintDefinition_in_constraint1032 = new BitSet(new long[] { 0x0010000000000000L });
	public static final BitSet FOLLOW_attributeConstraint_in_constraint1036 = new BitSet(new long[] { 0x0010000000000000L });
	public static final BitSet FOLLOW_SEMI_in_constraint1039 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1052 = new BitSet(new long[] { 0x0006E00000000002L });
	public static final BitSet FOLLOW_binaryOp_in_constraintDefinition1055 = new BitSet(new long[] { 0x0101000600000000L });
	public static final BitSet FOLLOW_constraintOperand_in_constraintDefinition1057 = new BitSet(new long[] { 0x0006E00000000002L });
	public static final BitSet FOLLOW_unaryOp_in_constraintOperand1084 = new BitSet(new long[] { 0x0101000600000000L });
	public static final BitSet FOLLOW_START_R_in_constraintOperand1088 = new BitSet(new long[] { 0x0101000600000000L });
	public static final BitSet FOLLOW_constraintDefinition_in_constraintOperand1090 = new BitSet(new long[] { 0x0000000002000000L });
	public static final BitSet FOLLOW_END_R_in_constraintOperand1092 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_name_in_constraintOperand1096 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_intAttribute_in_attribute1132 = new BitSet(new long[] { 0x0010000000000000L });
	public static final BitSet FOLLOW_floatAttribute_in_attribute1136 = new BitSet(new long[] { 0x0010000000000000L });
	public static final BitSet FOLLOW_stringAttribute_in_attribute1140 = new BitSet(new long[] { 0x0010000000000000L });
	public static final BitSet FOLLOW_boolAttribute_in_attribute1144 = new BitSet(new long[] { 0x0010000000000000L });
	public static final BitSet FOLLOW_SEMI_in_attribute1147 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_attribConstraint_in_attributeConstraint1178 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1198 = new BitSet(new long[] { 0x0008010000000A80L });
	public static final BitSet FOLLOW_attribOperator_in_attribConstraint1201 = new BitSet(new long[] { 0x0000004600000000L });
	public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1203 = new BitSet(new long[] { 0x0008010000000A80L });
	public static final BitSet FOLLOW_attribRelation_in_attribConstraint1211 = new BitSet(new long[] { 0x0000004600000000L });
	public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1217 = new BitSet(new long[] { 0x0008010000000002L });
	public static final BitSet FOLLOW_attribOperator_in_attribConstraint1220 = new BitSet(new long[] { 0x0000004600000000L });
	public static final BitSet FOLLOW_attribNumInstance_in_attribConstraint1222 = new BitSet(new long[] { 0x0008010000000002L });
	public static final BitSet FOLLOW_INT_in_attribNumInstance1254 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_name_in_attribNumInstance1261 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_VAR_INT_in_intAttribute1271 = new BitSet(new long[] { 0x0000000600000000L });
	public static final BitSet FOLLOW_name_in_intAttribute1274 = new BitSet(new long[] { 0x0000000004000002L });
	public static final BitSet FOLLOW_EQ_in_intAttribute1277 = new BitSet(new long[] { 0x0000004000000000L });
	public static final BitSet FOLLOW_INT_in_intAttribute1280 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_VAR_FLOAT_in_floatAttribute1289 = new BitSet(new long[] { 0x0000000600000000L });
	public static final BitSet FOLLOW_name_in_floatAttribute1292 = new BitSet(new long[] { 0x0000000004000002L });
	public static final BitSet FOLLOW_EQ_in_floatAttribute1295 = new BitSet(new long[] { 0x0000000040000000L });
	public static final BitSet FOLLOW_FLOAT_in_floatAttribute1298 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_VAR_STRING_in_stringAttribute1306 = new BitSet(new long[] { 0x0000000600000000L });
	public static final BitSet FOLLOW_name_in_stringAttribute1309 = new BitSet(new long[] { 0x0000000004000002L });
	public static final BitSet FOLLOW_EQ_in_stringAttribute1312 = new BitSet(new long[] { 0x0200000000000000L });
	public static final BitSet FOLLOW_STRING_in_stringAttribute1315 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_VAR_BOOL_in_boolAttribute1324 = new BitSet(new long[] { 0x0000000600000000L });
	public static final BitSet FOLLOW_name_in_boolAttribute1327 = new BitSet(new long[] { 0x0000000004000002L });
	public static final BitSet FOLLOW_EQ_in_boolAttribute1330 = new BitSet(new long[] { 0x0000000000004000L });
	public static final BitSet FOLLOW_BOOLEAN_in_boolAttribute1333 = new BitSet(new long[] { 0x0000000000000002L });
	public static final BitSet FOLLOW_OP_NOT_in_unaryOp1345 = new BitSet(new long[] { 0x0000000000000002L });

}
