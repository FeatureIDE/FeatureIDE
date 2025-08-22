// Generated from Velvet.g4 by ANTLR 4.13.2

package de.ovgu.featureide.fm.core.io.velvet;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast", "CheckReturnValue", "this-escape"})
public class VelvetParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.13.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		IMPORT=1, MANDATORY=2, ABSTRACT=3, SOMEOF=4, ONEOF=5, CONCEPT=6, CINTERFACE=7, 
		CONSTRAINT=8, FEATURE=9, USE=10, IMPORTINSTANCE=11, IMPORTINTERFACE=12, 
		DESCRIPTION=13, VAR_INT=14, VAR_FLOAT=15, VAR_STRING=16, VAR_BOOL=17, 
		SEMI=18, START_C=19, END_C=20, START_R=21, END_R=22, EQ=23, COMMA=24, 
		COLON=25, PLUS=26, MINUS=27, OP_NOT=28, OP_AND=29, OP_OR=30, OP_XOR=31, 
		OP_IMPLIES=32, OP_EQUIVALENT=33, ATTR_OP_EQUALS=34, ATTR_OP_NOT_EQUALS=35, 
		ATTR_OP_GREATER=36, ATTR_OP_LESS=37, ATTR_OP_GREATER_EQ=38, ATTR_OP_LESS_EQ=39, 
		EMPTY=40, CONSTR=41, ACONSTR=42, BASEEXT=43, DEF=44, GROUP=45, ATTR=46, 
		UNARYOP=47, OPERAND=48, BOOLEAN=49, ID=50, IDPath=51, INT=52, FLOAT=53, 
		STRING=54, WS=55, SL_COMMENT=56, ML_COMMENT=57;
	public static final int
		RULE_velvetModel = 0, RULE_imp = 1, RULE_concept = 2, RULE_cinterface = 3, 
		RULE_conceptBaseExt = 4, RULE_instanceImports = 5, RULE_interfaceImports = 6, 
		RULE_name = 7, RULE_definitions = 8, RULE_definition = 9, RULE_nonFeatureDefinition = 10, 
		RULE_use = 11, RULE_feature = 12, RULE_featureGroup = 13, RULE_groupType = 14, 
		RULE_description = 15, RULE_constraint = 16, RULE_constraintDefinition = 17, 
		RULE_constraintOperand = 18, RULE_attribute = 19, RULE_attributeConstraint = 20, 
		RULE_attribNumExpr = 21, RULE_attribOperator = 22, RULE_attribNumInstance = 23, 
		RULE_intAttribute = 24, RULE_floatAttribute = 25, RULE_stringAttribute = 26, 
		RULE_boolAttribute = 27, RULE_unaryOp = 28, RULE_binaryOp = 29, RULE_attribRelation = 30;
	private static String[] makeRuleNames() {
		return new String[] {
			"velvetModel", "imp", "concept", "cinterface", "conceptBaseExt", "instanceImports", 
			"interfaceImports", "name", "definitions", "definition", "nonFeatureDefinition", 
			"use", "feature", "featureGroup", "groupType", "description", "constraint", 
			"constraintDefinition", "constraintOperand", "attribute", "attributeConstraint", 
			"attribNumExpr", "attribOperator", "attribNumInstance", "intAttribute", 
			"floatAttribute", "stringAttribute", "boolAttribute", "unaryOp", "binaryOp", 
			"attribRelation"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'import'", "'mandatory'", "'abstract'", "'someOf'", "'oneOf'", 
			"'concept'", "'cinterface'", "'constraint'", "'feature'", "'use'", "'instance'", 
			"'interface'", "'description'", "'int'", "'float'", "'string'", "'bool'", 
			"';'", "'{'", "'}'", "'('", "')'", "'='", "','", "':'", "'+'", "'-'", 
			"'!'", "'&&'", "'||'", "'xor'", "'->'", "'<->'", "'=='", "'!='", "'>'", 
			"'<'", "'>='", "'<='", "'EMPTY'", "'CONSTR'", "'ACONSTR'", "'BASEEXT'", 
			"'DEF'", "'GROUP'", "'ATTR'", "'UNARYOP'", "'OPERAND'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "IMPORT", "MANDATORY", "ABSTRACT", "SOMEOF", "ONEOF", "CONCEPT", 
			"CINTERFACE", "CONSTRAINT", "FEATURE", "USE", "IMPORTINSTANCE", "IMPORTINTERFACE", 
			"DESCRIPTION", "VAR_INT", "VAR_FLOAT", "VAR_STRING", "VAR_BOOL", "SEMI", 
			"START_C", "END_C", "START_R", "END_R", "EQ", "COMMA", "COLON", "PLUS", 
			"MINUS", "OP_NOT", "OP_AND", "OP_OR", "OP_XOR", "OP_IMPLIES", "OP_EQUIVALENT", 
			"ATTR_OP_EQUALS", "ATTR_OP_NOT_EQUALS", "ATTR_OP_GREATER", "ATTR_OP_LESS", 
			"ATTR_OP_GREATER_EQ", "ATTR_OP_LESS_EQ", "EMPTY", "CONSTR", "ACONSTR", 
			"BASEEXT", "DEF", "GROUP", "ATTR", "UNARYOP", "OPERAND", "BOOLEAN", "ID", 
			"IDPath", "INT", "FLOAT", "STRING", "WS", "SL_COMMENT", "ML_COMMENT"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "Velvet.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }


	public class InternalSyntaxException extends RuntimeException{
		private final RecognitionException e;
		public InternalSyntaxException(RecognitionException e){
			this.e = e;	
		}
		
		public RecognitionException getException(){
			return e;
		}
	}

	public VelvetParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@SuppressWarnings("CheckReturnValue")
	public static class VelvetModelContext extends ParserRuleContext {
		public TerminalNode EOF() { return getToken(VelvetParser.EOF, 0); }
		public ConceptContext concept() {
			return getRuleContext(ConceptContext.class,0);
		}
		public CinterfaceContext cinterface() {
			return getRuleContext(CinterfaceContext.class,0);
		}
		public ImpContext imp() {
			return getRuleContext(ImpContext.class,0);
		}
		public VelvetModelContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_velvetModel; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterVelvetModel(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitVelvetModel(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitVelvetModel(this);
			else return visitor.visitChildren(this);
		}
	}

	public final VelvetModelContext velvetModel() throws RecognitionException {
		VelvetModelContext _localctx = new VelvetModelContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_velvetModel);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(63);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==IMPORT) {
				{
				setState(62);
				imp();
				}
			}

			setState(67);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case CONCEPT:
				{
				setState(65);
				concept();
				}
				break;
			case CINTERFACE:
				{
				setState(66);
				cinterface();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			setState(69);
			match(EOF);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ImpContext extends ParserRuleContext {
		public List<TerminalNode> IMPORT() { return getTokens(VelvetParser.IMPORT); }
		public TerminalNode IMPORT(int i) {
			return getToken(VelvetParser.IMPORT, i);
		}
		public List<NameContext> name() {
			return getRuleContexts(NameContext.class);
		}
		public NameContext name(int i) {
			return getRuleContext(NameContext.class,i);
		}
		public List<TerminalNode> SEMI() { return getTokens(VelvetParser.SEMI); }
		public TerminalNode SEMI(int i) {
			return getToken(VelvetParser.SEMI, i);
		}
		public ImpContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_imp; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterImp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitImp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitImp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ImpContext imp() throws RecognitionException {
		ImpContext _localctx = new ImpContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_imp);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(75); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(71);
				match(IMPORT);
				setState(72);
				name();
				setState(73);
				match(SEMI);
				}
				}
				setState(77); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( _la==IMPORT );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ConceptContext extends ParserRuleContext {
		public TerminalNode CONCEPT() { return getToken(VelvetParser.CONCEPT, 0); }
		public TerminalNode ID() { return getToken(VelvetParser.ID, 0); }
		public TerminalNode COLON() { return getToken(VelvetParser.COLON, 0); }
		public ConceptBaseExtContext conceptBaseExt() {
			return getRuleContext(ConceptBaseExtContext.class,0);
		}
		public InstanceImportsContext instanceImports() {
			return getRuleContext(InstanceImportsContext.class,0);
		}
		public InterfaceImportsContext interfaceImports() {
			return getRuleContext(InterfaceImportsContext.class,0);
		}
		public DefinitionsContext definitions() {
			return getRuleContext(DefinitionsContext.class,0);
		}
		public ConceptContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_concept; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterConcept(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitConcept(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitConcept(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ConceptContext concept() throws RecognitionException {
		ConceptContext _localctx = new ConceptContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_concept);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(79);
			match(CONCEPT);
			setState(80);
			match(ID);
			setState(83);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==COLON) {
				{
				setState(81);
				match(COLON);
				setState(82);
				conceptBaseExt();
				}
			}

			setState(93);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,4,_ctx) ) {
			case 1:
				{
				setState(85);
				instanceImports();
				setState(86);
				interfaceImports();
				}
				break;
			case 2:
				{
				setState(88);
				interfaceImports();
				setState(89);
				instanceImports();
				}
				break;
			case 3:
				{
				setState(91);
				interfaceImports();
				}
				break;
			case 4:
				{
				setState(92);
				instanceImports();
				}
				break;
			}
			setState(96);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==START_C) {
				{
				setState(95);
				definitions();
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class CinterfaceContext extends ParserRuleContext {
		public TerminalNode CINTERFACE() { return getToken(VelvetParser.CINTERFACE, 0); }
		public TerminalNode ID() { return getToken(VelvetParser.ID, 0); }
		public DefinitionsContext definitions() {
			return getRuleContext(DefinitionsContext.class,0);
		}
		public TerminalNode COLON() { return getToken(VelvetParser.COLON, 0); }
		public ConceptBaseExtContext conceptBaseExt() {
			return getRuleContext(ConceptBaseExtContext.class,0);
		}
		public CinterfaceContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_cinterface; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterCinterface(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitCinterface(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitCinterface(this);
			else return visitor.visitChildren(this);
		}
	}

	public final CinterfaceContext cinterface() throws RecognitionException {
		CinterfaceContext _localctx = new CinterfaceContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_cinterface);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(98);
			match(CINTERFACE);
			setState(99);
			match(ID);
			setState(102);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==COLON) {
				{
				setState(100);
				match(COLON);
				setState(101);
				conceptBaseExt();
				}
			}

			setState(104);
			definitions();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ConceptBaseExtContext extends ParserRuleContext {
		public List<TerminalNode> ID() { return getTokens(VelvetParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(VelvetParser.ID, i);
		}
		public List<TerminalNode> COMMA() { return getTokens(VelvetParser.COMMA); }
		public TerminalNode COMMA(int i) {
			return getToken(VelvetParser.COMMA, i);
		}
		public ConceptBaseExtContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_conceptBaseExt; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterConceptBaseExt(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitConceptBaseExt(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitConceptBaseExt(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ConceptBaseExtContext conceptBaseExt() throws RecognitionException {
		ConceptBaseExtContext _localctx = new ConceptBaseExtContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_conceptBaseExt);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(106);
			match(ID);
			setState(111);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==COMMA) {
				{
				{
				setState(107);
				match(COMMA);
				setState(108);
				match(ID);
				}
				}
				setState(113);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class InstanceImportsContext extends ParserRuleContext {
		public TerminalNode IMPORTINSTANCE() { return getToken(VelvetParser.IMPORTINSTANCE, 0); }
		public List<TerminalNode> ID() { return getTokens(VelvetParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(VelvetParser.ID, i);
		}
		public List<NameContext> name() {
			return getRuleContexts(NameContext.class);
		}
		public NameContext name(int i) {
			return getRuleContext(NameContext.class,i);
		}
		public List<TerminalNode> COMMA() { return getTokens(VelvetParser.COMMA); }
		public TerminalNode COMMA(int i) {
			return getToken(VelvetParser.COMMA, i);
		}
		public InstanceImportsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_instanceImports; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterInstanceImports(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitInstanceImports(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitInstanceImports(this);
			else return visitor.visitChildren(this);
		}
	}

	public final InstanceImportsContext instanceImports() throws RecognitionException {
		InstanceImportsContext _localctx = new InstanceImportsContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_instanceImports);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(114);
			match(IMPORTINSTANCE);
			setState(115);
			match(ID);
			setState(116);
			name();
			setState(122);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==COMMA) {
				{
				{
				setState(117);
				match(COMMA);
				setState(118);
				match(ID);
				setState(119);
				name();
				}
				}
				setState(124);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class InterfaceImportsContext extends ParserRuleContext {
		public TerminalNode IMPORTINTERFACE() { return getToken(VelvetParser.IMPORTINTERFACE, 0); }
		public List<TerminalNode> ID() { return getTokens(VelvetParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(VelvetParser.ID, i);
		}
		public List<NameContext> name() {
			return getRuleContexts(NameContext.class);
		}
		public NameContext name(int i) {
			return getRuleContext(NameContext.class,i);
		}
		public List<TerminalNode> COMMA() { return getTokens(VelvetParser.COMMA); }
		public TerminalNode COMMA(int i) {
			return getToken(VelvetParser.COMMA, i);
		}
		public InterfaceImportsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_interfaceImports; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterInterfaceImports(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitInterfaceImports(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitInterfaceImports(this);
			else return visitor.visitChildren(this);
		}
	}

	public final InterfaceImportsContext interfaceImports() throws RecognitionException {
		InterfaceImportsContext _localctx = new InterfaceImportsContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_interfaceImports);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(125);
			match(IMPORTINTERFACE);
			setState(126);
			match(ID);
			setState(127);
			name();
			setState(133);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==COMMA) {
				{
				{
				setState(128);
				match(COMMA);
				setState(129);
				match(ID);
				setState(130);
				name();
				}
				}
				setState(135);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class NameContext extends ParserRuleContext {
		public TerminalNode ID() { return getToken(VelvetParser.ID, 0); }
		public TerminalNode IDPath() { return getToken(VelvetParser.IDPath, 0); }
		public NameContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_name; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterName(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitName(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitName(this);
			else return visitor.visitChildren(this);
		}
	}

	public final NameContext name() throws RecognitionException {
		NameContext _localctx = new NameContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_name);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(136);
			_la = _input.LA(1);
			if ( !(_la==ID || _la==IDPath) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class DefinitionsContext extends ParserRuleContext {
		public TerminalNode START_C() { return getToken(VelvetParser.START_C, 0); }
		public DefinitionContext definition() {
			return getRuleContext(DefinitionContext.class,0);
		}
		public TerminalNode END_C() { return getToken(VelvetParser.END_C, 0); }
		public DefinitionsContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_definitions; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterDefinitions(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitDefinitions(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitDefinitions(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DefinitionsContext definitions() throws RecognitionException {
		DefinitionsContext _localctx = new DefinitionsContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_definitions);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(138);
			match(START_C);
			setState(139);
			definition();
			setState(140);
			match(END_C);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class DefinitionContext extends ParserRuleContext {
		public List<NonFeatureDefinitionContext> nonFeatureDefinition() {
			return getRuleContexts(NonFeatureDefinitionContext.class);
		}
		public NonFeatureDefinitionContext nonFeatureDefinition(int i) {
			return getRuleContext(NonFeatureDefinitionContext.class,i);
		}
		public FeatureGroupContext featureGroup() {
			return getRuleContext(FeatureGroupContext.class,0);
		}
		public List<FeatureContext> feature() {
			return getRuleContexts(FeatureContext.class);
		}
		public FeatureContext feature(int i) {
			return getRuleContext(FeatureContext.class,i);
		}
		public DefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_definition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DefinitionContext definition() throws RecognitionException {
		DefinitionContext _localctx = new DefinitionContext(_ctx, getState());
		enterRule(_localctx, 18, RULE_definition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(145);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & 255232L) != 0)) {
				{
				{
				setState(142);
				nonFeatureDefinition();
				}
				}
				setState(147);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(163);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case SOMEOF:
			case ONEOF:
				{
				{
				setState(148);
				featureGroup();
				setState(152);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while ((((_la) & ~0x3f) == 0 && ((1L << _la) & 255232L) != 0)) {
					{
					{
					setState(149);
					nonFeatureDefinition();
					}
					}
					setState(154);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
				}
				break;
			case MANDATORY:
			case ABSTRACT:
			case FEATURE:
				{
				{
				setState(155);
				feature();
				setState(160);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while ((((_la) & ~0x3f) == 0 && ((1L << _la) & 255756L) != 0)) {
					{
					setState(158);
					_errHandler.sync(this);
					switch (_input.LA(1)) {
					case MANDATORY:
					case ABSTRACT:
					case FEATURE:
						{
						setState(156);
						feature();
						}
						break;
					case CONSTRAINT:
					case USE:
					case DESCRIPTION:
					case VAR_INT:
					case VAR_FLOAT:
					case VAR_STRING:
					case VAR_BOOL:
						{
						setState(157);
						nonFeatureDefinition();
						}
						break;
					default:
						throw new NoViableAltException(this);
					}
					}
					setState(162);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
				}
				break;
			case END_C:
				break;
			default:
				break;
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class NonFeatureDefinitionContext extends ParserRuleContext {
		public ConstraintContext constraint() {
			return getRuleContext(ConstraintContext.class,0);
		}
		public UseContext use() {
			return getRuleContext(UseContext.class,0);
		}
		public AttributeContext attribute() {
			return getRuleContext(AttributeContext.class,0);
		}
		public DescriptionContext description() {
			return getRuleContext(DescriptionContext.class,0);
		}
		public NonFeatureDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_nonFeatureDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterNonFeatureDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitNonFeatureDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitNonFeatureDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final NonFeatureDefinitionContext nonFeatureDefinition() throws RecognitionException {
		NonFeatureDefinitionContext _localctx = new NonFeatureDefinitionContext(_ctx, getState());
		enterRule(_localctx, 20, RULE_nonFeatureDefinition);
		try {
			setState(169);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case CONSTRAINT:
				enterOuterAlt(_localctx, 1);
				{
				setState(165);
				constraint();
				}
				break;
			case USE:
				enterOuterAlt(_localctx, 2);
				{
				setState(166);
				use();
				}
				break;
			case VAR_INT:
			case VAR_FLOAT:
			case VAR_STRING:
			case VAR_BOOL:
				enterOuterAlt(_localctx, 3);
				{
				setState(167);
				attribute();
				}
				break;
			case DESCRIPTION:
				enterOuterAlt(_localctx, 4);
				{
				setState(168);
				description();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class UseContext extends ParserRuleContext {
		public TerminalNode USE() { return getToken(VelvetParser.USE, 0); }
		public NameContext name() {
			return getRuleContext(NameContext.class,0);
		}
		public TerminalNode SEMI() { return getToken(VelvetParser.SEMI, 0); }
		public UseContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_use; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterUse(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitUse(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitUse(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UseContext use() throws RecognitionException {
		UseContext _localctx = new UseContext(_ctx, getState());
		enterRule(_localctx, 22, RULE_use);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(171);
			match(USE);
			setState(172);
			name();
			setState(173);
			match(SEMI);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class FeatureContext extends ParserRuleContext {
		public TerminalNode FEATURE() { return getToken(VelvetParser.FEATURE, 0); }
		public NameContext name() {
			return getRuleContext(NameContext.class,0);
		}
		public DefinitionsContext definitions() {
			return getRuleContext(DefinitionsContext.class,0);
		}
		public TerminalNode SEMI() { return getToken(VelvetParser.SEMI, 0); }
		public TerminalNode MANDATORY() { return getToken(VelvetParser.MANDATORY, 0); }
		public TerminalNode ABSTRACT() { return getToken(VelvetParser.ABSTRACT, 0); }
		public FeatureContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_feature; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterFeature(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitFeature(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitFeature(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FeatureContext feature() throws RecognitionException {
		FeatureContext _localctx = new FeatureContext(_ctx, getState());
		enterRule(_localctx, 24, RULE_feature);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(181);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,16,_ctx) ) {
			case 1:
				{
				setState(175);
				match(MANDATORY);
				setState(176);
				match(ABSTRACT);
				}
				break;
			case 2:
				{
				setState(177);
				match(ABSTRACT);
				setState(178);
				match(MANDATORY);
				}
				break;
			case 3:
				{
				setState(179);
				match(MANDATORY);
				}
				break;
			case 4:
				{
				setState(180);
				match(ABSTRACT);
				}
				break;
			}
			setState(183);
			match(FEATURE);
			setState(184);
			name();
			setState(187);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case START_C:
				{
				setState(185);
				definitions();
				}
				break;
			case SEMI:
				{
				setState(186);
				match(SEMI);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class FeatureGroupContext extends ParserRuleContext {
		public GroupTypeContext groupType() {
			return getRuleContext(GroupTypeContext.class,0);
		}
		public TerminalNode START_C() { return getToken(VelvetParser.START_C, 0); }
		public TerminalNode END_C() { return getToken(VelvetParser.END_C, 0); }
		public List<FeatureContext> feature() {
			return getRuleContexts(FeatureContext.class);
		}
		public FeatureContext feature(int i) {
			return getRuleContext(FeatureContext.class,i);
		}
		public FeatureGroupContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_featureGroup; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterFeatureGroup(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitFeatureGroup(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitFeatureGroup(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FeatureGroupContext featureGroup() throws RecognitionException {
		FeatureGroupContext _localctx = new FeatureGroupContext(_ctx, getState());
		enterRule(_localctx, 26, RULE_featureGroup);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(189);
			groupType();
			setState(190);
			match(START_C);
			setState(192); 
			_errHandler.sync(this);
			_la = _input.LA(1);
			do {
				{
				{
				setState(191);
				feature();
				}
				}
				setState(194); 
				_errHandler.sync(this);
				_la = _input.LA(1);
			} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & 524L) != 0) );
			setState(196);
			match(END_C);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class GroupTypeContext extends ParserRuleContext {
		public TerminalNode SOMEOF() { return getToken(VelvetParser.SOMEOF, 0); }
		public TerminalNode ONEOF() { return getToken(VelvetParser.ONEOF, 0); }
		public GroupTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_groupType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterGroupType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitGroupType(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitGroupType(this);
			else return visitor.visitChildren(this);
		}
	}

	public final GroupTypeContext groupType() throws RecognitionException {
		GroupTypeContext _localctx = new GroupTypeContext(_ctx, getState());
		enterRule(_localctx, 28, RULE_groupType);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(198);
			_la = _input.LA(1);
			if ( !(_la==SOMEOF || _la==ONEOF) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class DescriptionContext extends ParserRuleContext {
		public TerminalNode DESCRIPTION() { return getToken(VelvetParser.DESCRIPTION, 0); }
		public TerminalNode STRING() { return getToken(VelvetParser.STRING, 0); }
		public TerminalNode SEMI() { return getToken(VelvetParser.SEMI, 0); }
		public DescriptionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_description; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterDescription(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitDescription(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitDescription(this);
			else return visitor.visitChildren(this);
		}
	}

	public final DescriptionContext description() throws RecognitionException {
		DescriptionContext _localctx = new DescriptionContext(_ctx, getState());
		enterRule(_localctx, 30, RULE_description);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(200);
			match(DESCRIPTION);
			setState(201);
			match(STRING);
			setState(202);
			match(SEMI);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ConstraintContext extends ParserRuleContext {
		public TerminalNode CONSTRAINT() { return getToken(VelvetParser.CONSTRAINT, 0); }
		public TerminalNode SEMI() { return getToken(VelvetParser.SEMI, 0); }
		public TerminalNode ID() { return getToken(VelvetParser.ID, 0); }
		public TerminalNode EQ() { return getToken(VelvetParser.EQ, 0); }
		public ConstraintDefinitionContext constraintDefinition() {
			return getRuleContext(ConstraintDefinitionContext.class,0);
		}
		public AttributeConstraintContext attributeConstraint() {
			return getRuleContext(AttributeConstraintContext.class,0);
		}
		public ConstraintContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_constraint; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterConstraint(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitConstraint(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitConstraint(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ConstraintContext constraint() throws RecognitionException {
		ConstraintContext _localctx = new ConstraintContext(_ctx, getState());
		enterRule(_localctx, 32, RULE_constraint);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(204);
			match(CONSTRAINT);
			{
			setState(205);
			match(ID);
			setState(206);
			match(EQ);
			}
			setState(210);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,19,_ctx) ) {
			case 1:
				{
				setState(208);
				constraintDefinition();
				}
				break;
			case 2:
				{
				setState(209);
				attributeConstraint();
				}
				break;
			}
			setState(212);
			match(SEMI);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ConstraintDefinitionContext extends ParserRuleContext {
		public List<ConstraintOperandContext> constraintOperand() {
			return getRuleContexts(ConstraintOperandContext.class);
		}
		public ConstraintOperandContext constraintOperand(int i) {
			return getRuleContext(ConstraintOperandContext.class,i);
		}
		public List<BinaryOpContext> binaryOp() {
			return getRuleContexts(BinaryOpContext.class);
		}
		public BinaryOpContext binaryOp(int i) {
			return getRuleContext(BinaryOpContext.class,i);
		}
		public ConstraintDefinitionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_constraintDefinition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterConstraintDefinition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitConstraintDefinition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitConstraintDefinition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ConstraintDefinitionContext constraintDefinition() throws RecognitionException {
		ConstraintDefinitionContext _localctx = new ConstraintDefinitionContext(_ctx, getState());
		enterRule(_localctx, 34, RULE_constraintDefinition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(214);
			constraintOperand();
			setState(220);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while ((((_la) & ~0x3f) == 0 && ((1L << _la) & 16642998272L) != 0)) {
				{
				{
				setState(215);
				binaryOp();
				setState(216);
				constraintOperand();
				}
				}
				setState(222);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ConstraintOperandContext extends ParserRuleContext {
		public TerminalNode START_R() { return getToken(VelvetParser.START_R, 0); }
		public ConstraintDefinitionContext constraintDefinition() {
			return getRuleContext(ConstraintDefinitionContext.class,0);
		}
		public TerminalNode END_R() { return getToken(VelvetParser.END_R, 0); }
		public NameContext name() {
			return getRuleContext(NameContext.class,0);
		}
		public List<UnaryOpContext> unaryOp() {
			return getRuleContexts(UnaryOpContext.class);
		}
		public UnaryOpContext unaryOp(int i) {
			return getRuleContext(UnaryOpContext.class,i);
		}
		public ConstraintOperandContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_constraintOperand; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterConstraintOperand(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitConstraintOperand(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitConstraintOperand(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ConstraintOperandContext constraintOperand() throws RecognitionException {
		ConstraintOperandContext _localctx = new ConstraintOperandContext(_ctx, getState());
		enterRule(_localctx, 36, RULE_constraintOperand);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(226);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==OP_NOT) {
				{
				{
				setState(223);
				unaryOp();
				}
				}
				setState(228);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(234);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case START_R:
				{
				setState(229);
				match(START_R);
				setState(230);
				constraintDefinition();
				setState(231);
				match(END_R);
				}
				break;
			case ID:
			case IDPath:
				{
				setState(233);
				name();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class AttributeContext extends ParserRuleContext {
		public TerminalNode SEMI() { return getToken(VelvetParser.SEMI, 0); }
		public IntAttributeContext intAttribute() {
			return getRuleContext(IntAttributeContext.class,0);
		}
		public FloatAttributeContext floatAttribute() {
			return getRuleContext(FloatAttributeContext.class,0);
		}
		public StringAttributeContext stringAttribute() {
			return getRuleContext(StringAttributeContext.class,0);
		}
		public BoolAttributeContext boolAttribute() {
			return getRuleContext(BoolAttributeContext.class,0);
		}
		public AttributeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_attribute; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterAttribute(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitAttribute(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitAttribute(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AttributeContext attribute() throws RecognitionException {
		AttributeContext _localctx = new AttributeContext(_ctx, getState());
		enterRule(_localctx, 38, RULE_attribute);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(240);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case VAR_INT:
				{
				setState(236);
				intAttribute();
				}
				break;
			case VAR_FLOAT:
				{
				setState(237);
				floatAttribute();
				}
				break;
			case VAR_STRING:
				{
				setState(238);
				stringAttribute();
				}
				break;
			case VAR_BOOL:
				{
				setState(239);
				boolAttribute();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			setState(242);
			match(SEMI);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class AttributeConstraintContext extends ParserRuleContext {
		public List<AttribNumExprContext> attribNumExpr() {
			return getRuleContexts(AttribNumExprContext.class);
		}
		public AttribNumExprContext attribNumExpr(int i) {
			return getRuleContext(AttribNumExprContext.class,i);
		}
		public AttribRelationContext attribRelation() {
			return getRuleContext(AttribRelationContext.class,0);
		}
		public AttributeConstraintContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_attributeConstraint; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterAttributeConstraint(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitAttributeConstraint(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitAttributeConstraint(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AttributeConstraintContext attributeConstraint() throws RecognitionException {
		AttributeConstraintContext _localctx = new AttributeConstraintContext(_ctx, getState());
		enterRule(_localctx, 40, RULE_attributeConstraint);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(244);
			attribNumExpr();
			setState(245);
			attribRelation();
			setState(246);
			attribNumExpr();
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class AttribNumExprContext extends ParserRuleContext {
		public List<AttribNumInstanceContext> attribNumInstance() {
			return getRuleContexts(AttribNumInstanceContext.class);
		}
		public AttribNumInstanceContext attribNumInstance(int i) {
			return getRuleContext(AttribNumInstanceContext.class,i);
		}
		public List<AttribOperatorContext> attribOperator() {
			return getRuleContexts(AttribOperatorContext.class);
		}
		public AttribOperatorContext attribOperator(int i) {
			return getRuleContext(AttribOperatorContext.class,i);
		}
		public AttribNumExprContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_attribNumExpr; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterAttribNumExpr(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitAttribNumExpr(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitAttribNumExpr(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AttribNumExprContext attribNumExpr() throws RecognitionException {
		AttribNumExprContext _localctx = new AttribNumExprContext(_ctx, getState());
		enterRule(_localctx, 42, RULE_attribNumExpr);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(248);
			attribNumInstance();
			setState(254);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==PLUS || _la==MINUS) {
				{
				{
				setState(249);
				attribOperator();
				setState(250);
				attribNumInstance();
				}
				}
				setState(256);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class AttribOperatorContext extends ParserRuleContext {
		public TerminalNode PLUS() { return getToken(VelvetParser.PLUS, 0); }
		public TerminalNode MINUS() { return getToken(VelvetParser.MINUS, 0); }
		public AttribOperatorContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_attribOperator; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterAttribOperator(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitAttribOperator(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitAttribOperator(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AttribOperatorContext attribOperator() throws RecognitionException {
		AttribOperatorContext _localctx = new AttribOperatorContext(_ctx, getState());
		enterRule(_localctx, 44, RULE_attribOperator);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(257);
			_la = _input.LA(1);
			if ( !(_la==PLUS || _la==MINUS) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class AttribNumInstanceContext extends ParserRuleContext {
		public TerminalNode INT() { return getToken(VelvetParser.INT, 0); }
		public NameContext name() {
			return getRuleContext(NameContext.class,0);
		}
		public AttribNumInstanceContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_attribNumInstance; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterAttribNumInstance(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitAttribNumInstance(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitAttribNumInstance(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AttribNumInstanceContext attribNumInstance() throws RecognitionException {
		AttribNumInstanceContext _localctx = new AttribNumInstanceContext(_ctx, getState());
		enterRule(_localctx, 46, RULE_attribNumInstance);
		try {
			setState(261);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case INT:
				enterOuterAlt(_localctx, 1);
				{
				setState(259);
				match(INT);
				}
				break;
			case ID:
			case IDPath:
				enterOuterAlt(_localctx, 2);
				{
				setState(260);
				name();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class IntAttributeContext extends ParserRuleContext {
		public TerminalNode VAR_INT() { return getToken(VelvetParser.VAR_INT, 0); }
		public NameContext name() {
			return getRuleContext(NameContext.class,0);
		}
		public TerminalNode EQ() { return getToken(VelvetParser.EQ, 0); }
		public TerminalNode INT() { return getToken(VelvetParser.INT, 0); }
		public IntAttributeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_intAttribute; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterIntAttribute(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitIntAttribute(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitIntAttribute(this);
			else return visitor.visitChildren(this);
		}
	}

	public final IntAttributeContext intAttribute() throws RecognitionException {
		IntAttributeContext _localctx = new IntAttributeContext(_ctx, getState());
		enterRule(_localctx, 48, RULE_intAttribute);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(263);
			match(VAR_INT);
			setState(264);
			name();
			setState(267);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==EQ) {
				{
				setState(265);
				match(EQ);
				setState(266);
				match(INT);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class FloatAttributeContext extends ParserRuleContext {
		public TerminalNode VAR_FLOAT() { return getToken(VelvetParser.VAR_FLOAT, 0); }
		public NameContext name() {
			return getRuleContext(NameContext.class,0);
		}
		public TerminalNode EQ() { return getToken(VelvetParser.EQ, 0); }
		public TerminalNode FLOAT() { return getToken(VelvetParser.FLOAT, 0); }
		public FloatAttributeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_floatAttribute; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterFloatAttribute(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitFloatAttribute(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitFloatAttribute(this);
			else return visitor.visitChildren(this);
		}
	}

	public final FloatAttributeContext floatAttribute() throws RecognitionException {
		FloatAttributeContext _localctx = new FloatAttributeContext(_ctx, getState());
		enterRule(_localctx, 50, RULE_floatAttribute);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(269);
			match(VAR_FLOAT);
			setState(270);
			name();
			setState(273);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==EQ) {
				{
				setState(271);
				match(EQ);
				setState(272);
				match(FLOAT);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class StringAttributeContext extends ParserRuleContext {
		public TerminalNode VAR_STRING() { return getToken(VelvetParser.VAR_STRING, 0); }
		public NameContext name() {
			return getRuleContext(NameContext.class,0);
		}
		public TerminalNode EQ() { return getToken(VelvetParser.EQ, 0); }
		public TerminalNode STRING() { return getToken(VelvetParser.STRING, 0); }
		public StringAttributeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_stringAttribute; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterStringAttribute(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitStringAttribute(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitStringAttribute(this);
			else return visitor.visitChildren(this);
		}
	}

	public final StringAttributeContext stringAttribute() throws RecognitionException {
		StringAttributeContext _localctx = new StringAttributeContext(_ctx, getState());
		enterRule(_localctx, 52, RULE_stringAttribute);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(275);
			match(VAR_STRING);
			setState(276);
			name();
			setState(279);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==EQ) {
				{
				setState(277);
				match(EQ);
				setState(278);
				match(STRING);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class BoolAttributeContext extends ParserRuleContext {
		public TerminalNode VAR_BOOL() { return getToken(VelvetParser.VAR_BOOL, 0); }
		public NameContext name() {
			return getRuleContext(NameContext.class,0);
		}
		public TerminalNode EQ() { return getToken(VelvetParser.EQ, 0); }
		public TerminalNode BOOLEAN() { return getToken(VelvetParser.BOOLEAN, 0); }
		public BoolAttributeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_boolAttribute; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterBoolAttribute(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitBoolAttribute(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitBoolAttribute(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BoolAttributeContext boolAttribute() throws RecognitionException {
		BoolAttributeContext _localctx = new BoolAttributeContext(_ctx, getState());
		enterRule(_localctx, 54, RULE_boolAttribute);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(281);
			match(VAR_BOOL);
			setState(282);
			name();
			setState(285);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==EQ) {
				{
				setState(283);
				match(EQ);
				setState(284);
				match(BOOLEAN);
				}
			}

			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class UnaryOpContext extends ParserRuleContext {
		public TerminalNode OP_NOT() { return getToken(VelvetParser.OP_NOT, 0); }
		public UnaryOpContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_unaryOp; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterUnaryOp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitUnaryOp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitUnaryOp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final UnaryOpContext unaryOp() throws RecognitionException {
		UnaryOpContext _localctx = new UnaryOpContext(_ctx, getState());
		enterRule(_localctx, 56, RULE_unaryOp);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(287);
			match(OP_NOT);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class BinaryOpContext extends ParserRuleContext {
		public TerminalNode OP_AND() { return getToken(VelvetParser.OP_AND, 0); }
		public TerminalNode OP_OR() { return getToken(VelvetParser.OP_OR, 0); }
		public TerminalNode OP_XOR() { return getToken(VelvetParser.OP_XOR, 0); }
		public TerminalNode OP_IMPLIES() { return getToken(VelvetParser.OP_IMPLIES, 0); }
		public TerminalNode OP_EQUIVALENT() { return getToken(VelvetParser.OP_EQUIVALENT, 0); }
		public BinaryOpContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_binaryOp; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterBinaryOp(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitBinaryOp(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitBinaryOp(this);
			else return visitor.visitChildren(this);
		}
	}

	public final BinaryOpContext binaryOp() throws RecognitionException {
		BinaryOpContext _localctx = new BinaryOpContext(_ctx, getState());
		enterRule(_localctx, 58, RULE_binaryOp);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(289);
			_la = _input.LA(1);
			if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 16642998272L) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class AttribRelationContext extends ParserRuleContext {
		public TerminalNode ATTR_OP_EQUALS() { return getToken(VelvetParser.ATTR_OP_EQUALS, 0); }
		public TerminalNode ATTR_OP_GREATER_EQ() { return getToken(VelvetParser.ATTR_OP_GREATER_EQ, 0); }
		public TerminalNode ATTR_OP_LESS_EQ() { return getToken(VelvetParser.ATTR_OP_LESS_EQ, 0); }
		public AttribRelationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_attribRelation; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).enterAttribRelation(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof VelvetListener ) ((VelvetListener)listener).exitAttribRelation(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof VelvetVisitor ) return ((VelvetVisitor<? extends T>)visitor).visitAttribRelation(this);
			else return visitor.visitChildren(this);
		}
	}

	public final AttribRelationContext attribRelation() throws RecognitionException {
		AttribRelationContext _localctx = new AttribRelationContext(_ctx, getState());
		enterRule(_localctx, 60, RULE_attribRelation);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(291);
			_la = _input.LA(1);
			if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 841813590016L) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\u0004\u00019\u0126\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001\u0002"+
		"\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004\u0002"+
		"\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007\u0002"+
		"\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b\u0007\u000b\u0002"+
		"\f\u0007\f\u0002\r\u0007\r\u0002\u000e\u0007\u000e\u0002\u000f\u0007\u000f"+
		"\u0002\u0010\u0007\u0010\u0002\u0011\u0007\u0011\u0002\u0012\u0007\u0012"+
		"\u0002\u0013\u0007\u0013\u0002\u0014\u0007\u0014\u0002\u0015\u0007\u0015"+
		"\u0002\u0016\u0007\u0016\u0002\u0017\u0007\u0017\u0002\u0018\u0007\u0018"+
		"\u0002\u0019\u0007\u0019\u0002\u001a\u0007\u001a\u0002\u001b\u0007\u001b"+
		"\u0002\u001c\u0007\u001c\u0002\u001d\u0007\u001d\u0002\u001e\u0007\u001e"+
		"\u0001\u0000\u0003\u0000@\b\u0000\u0001\u0000\u0001\u0000\u0003\u0000"+
		"D\b\u0000\u0001\u0000\u0001\u0000\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0004\u0001L\b\u0001\u000b\u0001\f\u0001M\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0001\u0002\u0003\u0002T\b\u0002\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001"+
		"\u0002\u0003\u0002^\b\u0002\u0001\u0002\u0003\u0002a\b\u0002\u0001\u0003"+
		"\u0001\u0003\u0001\u0003\u0001\u0003\u0003\u0003g\b\u0003\u0001\u0003"+
		"\u0001\u0003\u0001\u0004\u0001\u0004\u0001\u0004\u0005\u0004n\b\u0004"+
		"\n\u0004\f\u0004q\t\u0004\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005"+
		"\u0001\u0005\u0001\u0005\u0005\u0005y\b\u0005\n\u0005\f\u0005|\t\u0005"+
		"\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006\u0001\u0006"+
		"\u0005\u0006\u0084\b\u0006\n\u0006\f\u0006\u0087\t\u0006\u0001\u0007\u0001"+
		"\u0007\u0001\b\u0001\b\u0001\b\u0001\b\u0001\t\u0005\t\u0090\b\t\n\t\f"+
		"\t\u0093\t\t\u0001\t\u0001\t\u0005\t\u0097\b\t\n\t\f\t\u009a\t\t\u0001"+
		"\t\u0001\t\u0001\t\u0005\t\u009f\b\t\n\t\f\t\u00a2\t\t\u0003\t\u00a4\b"+
		"\t\u0001\n\u0001\n\u0001\n\u0001\n\u0003\n\u00aa\b\n\u0001\u000b\u0001"+
		"\u000b\u0001\u000b\u0001\u000b\u0001\f\u0001\f\u0001\f\u0001\f\u0001\f"+
		"\u0001\f\u0003\f\u00b6\b\f\u0001\f\u0001\f\u0001\f\u0001\f\u0003\f\u00bc"+
		"\b\f\u0001\r\u0001\r\u0001\r\u0004\r\u00c1\b\r\u000b\r\f\r\u00c2\u0001"+
		"\r\u0001\r\u0001\u000e\u0001\u000e\u0001\u000f\u0001\u000f\u0001\u000f"+
		"\u0001\u000f\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010\u0001\u0010"+
		"\u0001\u0010\u0003\u0010\u00d3\b\u0010\u0001\u0010\u0001\u0010\u0001\u0011"+
		"\u0001\u0011\u0001\u0011\u0001\u0011\u0005\u0011\u00db\b\u0011\n\u0011"+
		"\f\u0011\u00de\t\u0011\u0001\u0012\u0005\u0012\u00e1\b\u0012\n\u0012\f"+
		"\u0012\u00e4\t\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0001\u0012\u0001"+
		"\u0012\u0003\u0012\u00eb\b\u0012\u0001\u0013\u0001\u0013\u0001\u0013\u0001"+
		"\u0013\u0003\u0013\u00f1\b\u0013\u0001\u0013\u0001\u0013\u0001\u0014\u0001"+
		"\u0014\u0001\u0014\u0001\u0014\u0001\u0015\u0001\u0015\u0001\u0015\u0001"+
		"\u0015\u0005\u0015\u00fd\b\u0015\n\u0015\f\u0015\u0100\t\u0015\u0001\u0016"+
		"\u0001\u0016\u0001\u0017\u0001\u0017\u0003\u0017\u0106\b\u0017\u0001\u0018"+
		"\u0001\u0018\u0001\u0018\u0001\u0018\u0003\u0018\u010c\b\u0018\u0001\u0019"+
		"\u0001\u0019\u0001\u0019\u0001\u0019\u0003\u0019\u0112\b\u0019\u0001\u001a"+
		"\u0001\u001a\u0001\u001a\u0001\u001a\u0003\u001a\u0118\b\u001a\u0001\u001b"+
		"\u0001\u001b\u0001\u001b\u0001\u001b\u0003\u001b\u011e\b\u001b\u0001\u001c"+
		"\u0001\u001c\u0001\u001d\u0001\u001d\u0001\u001e\u0001\u001e\u0001\u001e"+
		"\u0000\u0000\u001f\u0000\u0002\u0004\u0006\b\n\f\u000e\u0010\u0012\u0014"+
		"\u0016\u0018\u001a\u001c\u001e \"$&(*,.02468:<\u0000\u0005\u0001\u0000"+
		"23\u0001\u0000\u0004\u0005\u0001\u0000\u001a\u001b\u0001\u0000\u001d!"+
		"\u0002\u0000\"\"&\'\u012f\u0000?\u0001\u0000\u0000\u0000\u0002K\u0001"+
		"\u0000\u0000\u0000\u0004O\u0001\u0000\u0000\u0000\u0006b\u0001\u0000\u0000"+
		"\u0000\bj\u0001\u0000\u0000\u0000\nr\u0001\u0000\u0000\u0000\f}\u0001"+
		"\u0000\u0000\u0000\u000e\u0088\u0001\u0000\u0000\u0000\u0010\u008a\u0001"+
		"\u0000\u0000\u0000\u0012\u0091\u0001\u0000\u0000\u0000\u0014\u00a9\u0001"+
		"\u0000\u0000\u0000\u0016\u00ab\u0001\u0000\u0000\u0000\u0018\u00b5\u0001"+
		"\u0000\u0000\u0000\u001a\u00bd\u0001\u0000\u0000\u0000\u001c\u00c6\u0001"+
		"\u0000\u0000\u0000\u001e\u00c8\u0001\u0000\u0000\u0000 \u00cc\u0001\u0000"+
		"\u0000\u0000\"\u00d6\u0001\u0000\u0000\u0000$\u00e2\u0001\u0000\u0000"+
		"\u0000&\u00f0\u0001\u0000\u0000\u0000(\u00f4\u0001\u0000\u0000\u0000*"+
		"\u00f8\u0001\u0000\u0000\u0000,\u0101\u0001\u0000\u0000\u0000.\u0105\u0001"+
		"\u0000\u0000\u00000\u0107\u0001\u0000\u0000\u00002\u010d\u0001\u0000\u0000"+
		"\u00004\u0113\u0001\u0000\u0000\u00006\u0119\u0001\u0000\u0000\u00008"+
		"\u011f\u0001\u0000\u0000\u0000:\u0121\u0001\u0000\u0000\u0000<\u0123\u0001"+
		"\u0000\u0000\u0000>@\u0003\u0002\u0001\u0000?>\u0001\u0000\u0000\u0000"+
		"?@\u0001\u0000\u0000\u0000@C\u0001\u0000\u0000\u0000AD\u0003\u0004\u0002"+
		"\u0000BD\u0003\u0006\u0003\u0000CA\u0001\u0000\u0000\u0000CB\u0001\u0000"+
		"\u0000\u0000DE\u0001\u0000\u0000\u0000EF\u0005\u0000\u0000\u0001F\u0001"+
		"\u0001\u0000\u0000\u0000GH\u0005\u0001\u0000\u0000HI\u0003\u000e\u0007"+
		"\u0000IJ\u0005\u0012\u0000\u0000JL\u0001\u0000\u0000\u0000KG\u0001\u0000"+
		"\u0000\u0000LM\u0001\u0000\u0000\u0000MK\u0001\u0000\u0000\u0000MN\u0001"+
		"\u0000\u0000\u0000N\u0003\u0001\u0000\u0000\u0000OP\u0005\u0006\u0000"+
		"\u0000PS\u00052\u0000\u0000QR\u0005\u0019\u0000\u0000RT\u0003\b\u0004"+
		"\u0000SQ\u0001\u0000\u0000\u0000ST\u0001\u0000\u0000\u0000T]\u0001\u0000"+
		"\u0000\u0000UV\u0003\n\u0005\u0000VW\u0003\f\u0006\u0000W^\u0001\u0000"+
		"\u0000\u0000XY\u0003\f\u0006\u0000YZ\u0003\n\u0005\u0000Z^\u0001\u0000"+
		"\u0000\u0000[^\u0003\f\u0006\u0000\\^\u0003\n\u0005\u0000]U\u0001\u0000"+
		"\u0000\u0000]X\u0001\u0000\u0000\u0000][\u0001\u0000\u0000\u0000]\\\u0001"+
		"\u0000\u0000\u0000]^\u0001\u0000\u0000\u0000^`\u0001\u0000\u0000\u0000"+
		"_a\u0003\u0010\b\u0000`_\u0001\u0000\u0000\u0000`a\u0001\u0000\u0000\u0000"+
		"a\u0005\u0001\u0000\u0000\u0000bc\u0005\u0007\u0000\u0000cf\u00052\u0000"+
		"\u0000de\u0005\u0019\u0000\u0000eg\u0003\b\u0004\u0000fd\u0001\u0000\u0000"+
		"\u0000fg\u0001\u0000\u0000\u0000gh\u0001\u0000\u0000\u0000hi\u0003\u0010"+
		"\b\u0000i\u0007\u0001\u0000\u0000\u0000jo\u00052\u0000\u0000kl\u0005\u0018"+
		"\u0000\u0000ln\u00052\u0000\u0000mk\u0001\u0000\u0000\u0000nq\u0001\u0000"+
		"\u0000\u0000om\u0001\u0000\u0000\u0000op\u0001\u0000\u0000\u0000p\t\u0001"+
		"\u0000\u0000\u0000qo\u0001\u0000\u0000\u0000rs\u0005\u000b\u0000\u0000"+
		"st\u00052\u0000\u0000tz\u0003\u000e\u0007\u0000uv\u0005\u0018\u0000\u0000"+
		"vw\u00052\u0000\u0000wy\u0003\u000e\u0007\u0000xu\u0001\u0000\u0000\u0000"+
		"y|\u0001\u0000\u0000\u0000zx\u0001\u0000\u0000\u0000z{\u0001\u0000\u0000"+
		"\u0000{\u000b\u0001\u0000\u0000\u0000|z\u0001\u0000\u0000\u0000}~\u0005"+
		"\f\u0000\u0000~\u007f\u00052\u0000\u0000\u007f\u0085\u0003\u000e\u0007"+
		"\u0000\u0080\u0081\u0005\u0018\u0000\u0000\u0081\u0082\u00052\u0000\u0000"+
		"\u0082\u0084\u0003\u000e\u0007\u0000\u0083\u0080\u0001\u0000\u0000\u0000"+
		"\u0084\u0087\u0001\u0000\u0000\u0000\u0085\u0083\u0001\u0000\u0000\u0000"+
		"\u0085\u0086\u0001\u0000\u0000\u0000\u0086\r\u0001\u0000\u0000\u0000\u0087"+
		"\u0085\u0001\u0000\u0000\u0000\u0088\u0089\u0007\u0000\u0000\u0000\u0089"+
		"\u000f\u0001\u0000\u0000\u0000\u008a\u008b\u0005\u0013\u0000\u0000\u008b"+
		"\u008c\u0003\u0012\t\u0000\u008c\u008d\u0005\u0014\u0000\u0000\u008d\u0011"+
		"\u0001\u0000\u0000\u0000\u008e\u0090\u0003\u0014\n\u0000\u008f\u008e\u0001"+
		"\u0000\u0000\u0000\u0090\u0093\u0001\u0000\u0000\u0000\u0091\u008f\u0001"+
		"\u0000\u0000\u0000\u0091\u0092\u0001\u0000\u0000\u0000\u0092\u00a3\u0001"+
		"\u0000\u0000\u0000\u0093\u0091\u0001\u0000\u0000\u0000\u0094\u0098\u0003"+
		"\u001a\r\u0000\u0095\u0097\u0003\u0014\n\u0000\u0096\u0095\u0001\u0000"+
		"\u0000\u0000\u0097\u009a\u0001\u0000\u0000\u0000\u0098\u0096\u0001\u0000"+
		"\u0000\u0000\u0098\u0099\u0001\u0000\u0000\u0000\u0099\u00a4\u0001\u0000"+
		"\u0000\u0000\u009a\u0098\u0001\u0000\u0000\u0000\u009b\u00a0\u0003\u0018"+
		"\f\u0000\u009c\u009f\u0003\u0018\f\u0000\u009d\u009f\u0003\u0014\n\u0000"+
		"\u009e\u009c\u0001\u0000\u0000\u0000\u009e\u009d\u0001\u0000\u0000\u0000"+
		"\u009f\u00a2\u0001\u0000\u0000\u0000\u00a0\u009e\u0001\u0000\u0000\u0000"+
		"\u00a0\u00a1\u0001\u0000\u0000\u0000\u00a1\u00a4\u0001\u0000\u0000\u0000"+
		"\u00a2\u00a0\u0001\u0000\u0000\u0000\u00a3\u0094\u0001\u0000\u0000\u0000"+
		"\u00a3\u009b\u0001\u0000\u0000\u0000\u00a3\u00a4\u0001\u0000\u0000\u0000"+
		"\u00a4\u0013\u0001\u0000\u0000\u0000\u00a5\u00aa\u0003 \u0010\u0000\u00a6"+
		"\u00aa\u0003\u0016\u000b\u0000\u00a7\u00aa\u0003&\u0013\u0000\u00a8\u00aa"+
		"\u0003\u001e\u000f\u0000\u00a9\u00a5\u0001\u0000\u0000\u0000\u00a9\u00a6"+
		"\u0001\u0000\u0000\u0000\u00a9\u00a7\u0001\u0000\u0000\u0000\u00a9\u00a8"+
		"\u0001\u0000\u0000\u0000\u00aa\u0015\u0001\u0000\u0000\u0000\u00ab\u00ac"+
		"\u0005\n\u0000\u0000\u00ac\u00ad\u0003\u000e\u0007\u0000\u00ad\u00ae\u0005"+
		"\u0012\u0000\u0000\u00ae\u0017\u0001\u0000\u0000\u0000\u00af\u00b0\u0005"+
		"\u0002\u0000\u0000\u00b0\u00b6\u0005\u0003\u0000\u0000\u00b1\u00b2\u0005"+
		"\u0003\u0000\u0000\u00b2\u00b6\u0005\u0002\u0000\u0000\u00b3\u00b6\u0005"+
		"\u0002\u0000\u0000\u00b4\u00b6\u0005\u0003\u0000\u0000\u00b5\u00af\u0001"+
		"\u0000\u0000\u0000\u00b5\u00b1\u0001\u0000\u0000\u0000\u00b5\u00b3\u0001"+
		"\u0000\u0000\u0000\u00b5\u00b4\u0001\u0000\u0000\u0000\u00b5\u00b6\u0001"+
		"\u0000\u0000\u0000\u00b6\u00b7\u0001\u0000\u0000\u0000\u00b7\u00b8\u0005"+
		"\t\u0000\u0000\u00b8\u00bb\u0003\u000e\u0007\u0000\u00b9\u00bc\u0003\u0010"+
		"\b\u0000\u00ba\u00bc\u0005\u0012\u0000\u0000\u00bb\u00b9\u0001\u0000\u0000"+
		"\u0000\u00bb\u00ba\u0001\u0000\u0000\u0000\u00bc\u0019\u0001\u0000\u0000"+
		"\u0000\u00bd\u00be\u0003\u001c\u000e\u0000\u00be\u00c0\u0005\u0013\u0000"+
		"\u0000\u00bf\u00c1\u0003\u0018\f\u0000\u00c0\u00bf\u0001\u0000\u0000\u0000"+
		"\u00c1\u00c2\u0001\u0000\u0000\u0000\u00c2\u00c0\u0001\u0000\u0000\u0000"+
		"\u00c2\u00c3\u0001\u0000\u0000\u0000\u00c3\u00c4\u0001\u0000\u0000\u0000"+
		"\u00c4\u00c5\u0005\u0014\u0000\u0000\u00c5\u001b\u0001\u0000\u0000\u0000"+
		"\u00c6\u00c7\u0007\u0001\u0000\u0000\u00c7\u001d\u0001\u0000\u0000\u0000"+
		"\u00c8\u00c9\u0005\r\u0000\u0000\u00c9\u00ca\u00056\u0000\u0000\u00ca"+
		"\u00cb\u0005\u0012\u0000\u0000\u00cb\u001f\u0001\u0000\u0000\u0000\u00cc"+
		"\u00cd\u0005\b\u0000\u0000\u00cd\u00ce\u00052\u0000\u0000\u00ce\u00cf"+
		"\u0005\u0017\u0000\u0000\u00cf\u00d2\u0001\u0000\u0000\u0000\u00d0\u00d3"+
		"\u0003\"\u0011\u0000\u00d1\u00d3\u0003(\u0014\u0000\u00d2\u00d0\u0001"+
		"\u0000\u0000\u0000\u00d2\u00d1\u0001\u0000\u0000\u0000\u00d3\u00d4\u0001"+
		"\u0000\u0000\u0000\u00d4\u00d5\u0005\u0012\u0000\u0000\u00d5!\u0001\u0000"+
		"\u0000\u0000\u00d6\u00dc\u0003$\u0012\u0000\u00d7\u00d8\u0003:\u001d\u0000"+
		"\u00d8\u00d9\u0003$\u0012\u0000\u00d9\u00db\u0001\u0000\u0000\u0000\u00da"+
		"\u00d7\u0001\u0000\u0000\u0000\u00db\u00de\u0001\u0000\u0000\u0000\u00dc"+
		"\u00da\u0001\u0000\u0000\u0000\u00dc\u00dd\u0001\u0000\u0000\u0000\u00dd"+
		"#\u0001\u0000\u0000\u0000\u00de\u00dc\u0001\u0000\u0000\u0000\u00df\u00e1"+
		"\u00038\u001c\u0000\u00e0\u00df\u0001\u0000\u0000\u0000\u00e1\u00e4\u0001"+
		"\u0000\u0000\u0000\u00e2\u00e0\u0001\u0000\u0000\u0000\u00e2\u00e3\u0001"+
		"\u0000\u0000\u0000\u00e3\u00ea\u0001\u0000\u0000\u0000\u00e4\u00e2\u0001"+
		"\u0000\u0000\u0000\u00e5\u00e6\u0005\u0015\u0000\u0000\u00e6\u00e7\u0003"+
		"\"\u0011\u0000\u00e7\u00e8\u0005\u0016\u0000\u0000\u00e8\u00eb\u0001\u0000"+
		"\u0000\u0000\u00e9\u00eb\u0003\u000e\u0007\u0000\u00ea\u00e5\u0001\u0000"+
		"\u0000\u0000\u00ea\u00e9\u0001\u0000\u0000\u0000\u00eb%\u0001\u0000\u0000"+
		"\u0000\u00ec\u00f1\u00030\u0018\u0000\u00ed\u00f1\u00032\u0019\u0000\u00ee"+
		"\u00f1\u00034\u001a\u0000\u00ef\u00f1\u00036\u001b\u0000\u00f0\u00ec\u0001"+
		"\u0000\u0000\u0000\u00f0\u00ed\u0001\u0000\u0000\u0000\u00f0\u00ee\u0001"+
		"\u0000\u0000\u0000\u00f0\u00ef\u0001\u0000\u0000\u0000\u00f1\u00f2\u0001"+
		"\u0000\u0000\u0000\u00f2\u00f3\u0005\u0012\u0000\u0000\u00f3\'\u0001\u0000"+
		"\u0000\u0000\u00f4\u00f5\u0003*\u0015\u0000\u00f5\u00f6\u0003<\u001e\u0000"+
		"\u00f6\u00f7\u0003*\u0015\u0000\u00f7)\u0001\u0000\u0000\u0000\u00f8\u00fe"+
		"\u0003.\u0017\u0000\u00f9\u00fa\u0003,\u0016\u0000\u00fa\u00fb\u0003."+
		"\u0017\u0000\u00fb\u00fd\u0001\u0000\u0000\u0000\u00fc\u00f9\u0001\u0000"+
		"\u0000\u0000\u00fd\u0100\u0001\u0000\u0000\u0000\u00fe\u00fc\u0001\u0000"+
		"\u0000\u0000\u00fe\u00ff\u0001\u0000\u0000\u0000\u00ff+\u0001\u0000\u0000"+
		"\u0000\u0100\u00fe\u0001\u0000\u0000\u0000\u0101\u0102\u0007\u0002\u0000"+
		"\u0000\u0102-\u0001\u0000\u0000\u0000\u0103\u0106\u00054\u0000\u0000\u0104"+
		"\u0106\u0003\u000e\u0007\u0000\u0105\u0103\u0001\u0000\u0000\u0000\u0105"+
		"\u0104\u0001\u0000\u0000\u0000\u0106/\u0001\u0000\u0000\u0000\u0107\u0108"+
		"\u0005\u000e\u0000\u0000\u0108\u010b\u0003\u000e\u0007\u0000\u0109\u010a"+
		"\u0005\u0017\u0000\u0000\u010a\u010c\u00054\u0000\u0000\u010b\u0109\u0001"+
		"\u0000\u0000\u0000\u010b\u010c\u0001\u0000\u0000\u0000\u010c1\u0001\u0000"+
		"\u0000\u0000\u010d\u010e\u0005\u000f\u0000\u0000\u010e\u0111\u0003\u000e"+
		"\u0007\u0000\u010f\u0110\u0005\u0017\u0000\u0000\u0110\u0112\u00055\u0000"+
		"\u0000\u0111\u010f\u0001\u0000\u0000\u0000\u0111\u0112\u0001\u0000\u0000"+
		"\u0000\u01123\u0001\u0000\u0000\u0000\u0113\u0114\u0005\u0010\u0000\u0000"+
		"\u0114\u0117\u0003\u000e\u0007\u0000\u0115\u0116\u0005\u0017\u0000\u0000"+
		"\u0116\u0118\u00056\u0000\u0000\u0117\u0115\u0001\u0000\u0000\u0000\u0117"+
		"\u0118\u0001\u0000\u0000\u0000\u01185\u0001\u0000\u0000\u0000\u0119\u011a"+
		"\u0005\u0011\u0000\u0000\u011a\u011d\u0003\u000e\u0007\u0000\u011b\u011c"+
		"\u0005\u0017\u0000\u0000\u011c\u011e\u00051\u0000\u0000\u011d\u011b\u0001"+
		"\u0000\u0000\u0000\u011d\u011e\u0001\u0000\u0000\u0000\u011e7\u0001\u0000"+
		"\u0000\u0000\u011f\u0120\u0005\u001c\u0000\u0000\u01209\u0001\u0000\u0000"+
		"\u0000\u0121\u0122\u0007\u0003\u0000\u0000\u0122;\u0001\u0000\u0000\u0000"+
		"\u0123\u0124\u0007\u0004\u0000\u0000\u0124=\u0001\u0000\u0000\u0000\u001e"+
		"?CMS]`foz\u0085\u0091\u0098\u009e\u00a0\u00a3\u00a9\u00b5\u00bb\u00c2"+
		"\u00d2\u00dc\u00e2\u00ea\u00f0\u00fe\u0105\u010b\u0111\u0117\u011d";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}