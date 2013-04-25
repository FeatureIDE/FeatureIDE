package org.deltaj.serializer;

import com.google.inject.Inject;
import com.google.inject.Provider;
import org.deltaj.deltaj.And;
import org.deltaj.deltaj.AndOrExpression;
import org.deltaj.deltaj.ArithmeticSigned;
import org.deltaj.deltaj.Assignment;
import org.deltaj.deltaj.BoolConstant;
import org.deltaj.deltaj.BooleanNegation;
import org.deltaj.deltaj.BooleanType;
import org.deltaj.deltaj.Cast;
import org.deltaj.deltaj.ClassAddition;
import org.deltaj.deltaj.ClassModification;
import org.deltaj.deltaj.ClassRemoval;
import org.deltaj.deltaj.ClassType;
import org.deltaj.deltaj.Comparison;
import org.deltaj.deltaj.Configuration;
import org.deltaj.deltaj.Configurations;
import org.deltaj.deltaj.DeltaModule;
import org.deltaj.deltaj.DeltaPartition;
import org.deltaj.deltaj.DeltajPackage;
import org.deltaj.deltaj.ExpressionStatement;
import org.deltaj.deltaj.Feature;
import org.deltaj.deltaj.FeatureRef;
import org.deltaj.deltaj.Features;
import org.deltaj.deltaj.Field;
import org.deltaj.deltaj.FieldAddition;
import org.deltaj.deltaj.FieldRemoval;
import org.deltaj.deltaj.FieldSelection;
import org.deltaj.deltaj.IfStatement;
import org.deltaj.deltaj.IntConstant;
import org.deltaj.deltaj.IntType;
import org.deltaj.deltaj.JavaVerbatim;
import org.deltaj.deltaj.LocalVariableDeclaration;
import org.deltaj.deltaj.Method;
import org.deltaj.deltaj.MethodAddition;
import org.deltaj.deltaj.MethodCall;
import org.deltaj.deltaj.MethodModification;
import org.deltaj.deltaj.MethodRemoval;
import org.deltaj.deltaj.Minus;
import org.deltaj.deltaj.ModuleReference;
import org.deltaj.deltaj.MultiOrDiv;
import org.deltaj.deltaj.Negation;
import org.deltaj.deltaj.New;
import org.deltaj.deltaj.Null;
import org.deltaj.deltaj.Or;
import org.deltaj.deltaj.Original;
import org.deltaj.deltaj.Parameter;
import org.deltaj.deltaj.Paren;
import org.deltaj.deltaj.PartitionPart;
import org.deltaj.deltaj.Plus;
import org.deltaj.deltaj.Product;
import org.deltaj.deltaj.ProductLine;
import org.deltaj.deltaj.Program;
import org.deltaj.deltaj.PropFalse;
import org.deltaj.deltaj.PropParen;
import org.deltaj.deltaj.PropTrue;
import org.deltaj.deltaj.ReturnStatement;
import org.deltaj.deltaj.Selection;
import org.deltaj.deltaj.StatementBlock;
import org.deltaj.deltaj.StringConstant;
import org.deltaj.deltaj.StringType;
import org.deltaj.deltaj.This;
import org.deltaj.deltaj.TypeVariable;
import org.deltaj.deltaj.VariableAccess;
import org.deltaj.deltaj.VoidType;
import org.deltaj.services.DeltaJGrammarAccess;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.serializer.acceptor.ISemanticSequenceAcceptor;
import org.eclipse.xtext.serializer.acceptor.SequenceFeeder;
import org.eclipse.xtext.serializer.diagnostic.ISemanticSequencerDiagnosticProvider;
import org.eclipse.xtext.serializer.diagnostic.ISerializationDiagnostic.Acceptor;
import org.eclipse.xtext.serializer.sequencer.AbstractSemanticSequencer;
import org.eclipse.xtext.serializer.sequencer.GenericSequencer;
import org.eclipse.xtext.serializer.sequencer.ISemanticNodeProvider.INodesForEObjectProvider;
import org.eclipse.xtext.serializer.sequencer.ISemanticSequencer;
import org.eclipse.xtext.serializer.sequencer.ITransientValueService;
import org.eclipse.xtext.serializer.sequencer.ITransientValueService.ValueTransient;

@SuppressWarnings("restriction")
public class AbstractDeltaJSemanticSequencer extends AbstractSemanticSequencer {

	@Inject
	protected DeltaJGrammarAccess grammarAccess;
	
	@Inject
	protected ISemanticSequencerDiagnosticProvider diagnosticProvider;
	
	@Inject
	protected ITransientValueService transientValues;
	
	@Inject
	@GenericSequencer
	protected Provider<ISemanticSequencer> genericSequencerProvider;
	
	protected ISemanticSequencer genericSequencer;
	
	
	@Override
	public void init(ISemanticSequencer sequencer, ISemanticSequenceAcceptor sequenceAcceptor, Acceptor errorAcceptor) {
		super.init(sequencer, sequenceAcceptor, errorAcceptor);
		this.genericSequencer = genericSequencerProvider.get();
		this.genericSequencer.init(sequencer, sequenceAcceptor, errorAcceptor);
	}
	
	public void createSequence(EObject context, EObject semanticObject) {
		if(semanticObject.eClass().getEPackage() == DeltajPackage.eINSTANCE) switch(semanticObject.eClass().getClassifierID()) {
			case DeltajPackage.AND:
				if(context == grammarAccess.getAndRule() ||
				   context == grammarAccess.getAndAccess().getAndLeftAction_1_0() ||
				   context == grammarAccess.getPropositionalFormulaRule() ||
				   context == grammarAccess.getPropositionalFormulaAccess().getOrLeftAction_1_0()) {
					sequence_And(context, (And) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.AND_OR_EXPRESSION:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0()) {
					sequence_BooleanExpression(context, (AndOrExpression) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.ARITHMETIC_SIGNED:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0()) {
					sequence_Atomic(context, (ArithmeticSigned) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.ASSIGNMENT:
				if(context == grammarAccess.getAssignmentRule() ||
				   context == grammarAccess.getStatementRule()) {
					sequence_Assignment(context, (Assignment) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.BOOL_CONSTANT:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0() ||
				   context == grammarAccess.getBoolConstantRule() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getConstantRule() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0() ||
				   context == grammarAccess.getTerminalExpressionRule()) {
					sequence_BoolConstant(context, (BoolConstant) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.BOOLEAN_NEGATION:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0()) {
					sequence_Atomic(context, (BooleanNegation) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.BOOLEAN_TYPE:
				if(context == grammarAccess.getBasicTypeRule() ||
				   context == grammarAccess.getBooleanTypeRule() ||
				   context == grammarAccess.getTypeRule() ||
				   context == grammarAccess.getTypeForDeclarationRule() ||
				   context == grammarAccess.getTypeForMethodRule()) {
					sequence_BooleanType(context, (BooleanType) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.CAST:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getCastRule() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0() ||
				   context == grammarAccess.getTerminalExpressionRule()) {
					sequence_Cast(context, (Cast) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.CLASS:
				if(context == grammarAccess.getClassRule()) {
					sequence_Class(context, (org.deltaj.deltaj.Class) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.CLASS_ADDITION:
				if(context == grammarAccess.getClassAdditionRule() ||
				   context == grammarAccess.getDeltaActionRule()) {
					sequence_ClassAddition(context, (ClassAddition) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.CLASS_MODIFICATION:
				if(context == grammarAccess.getClassModificationRule() ||
				   context == grammarAccess.getDeltaActionRule() ||
				   context == grammarAccess.getRemovesOrModifiesClassRule()) {
					sequence_ClassModification(context, (ClassModification) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.CLASS_REMOVAL:
				if(context == grammarAccess.getClassRemovalRule() ||
				   context == grammarAccess.getDeltaActionRule() ||
				   context == grammarAccess.getRemovesOrModifiesClassRule()) {
					sequence_ClassRemoval(context, (ClassRemoval) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.CLASS_TYPE:
				if(context == grammarAccess.getClassTypeRule() ||
				   context == grammarAccess.getTypeRule() ||
				   context == grammarAccess.getTypeForDeclarationRule() ||
				   context == grammarAccess.getTypeForMethodRule()) {
					sequence_ClassType(context, (ClassType) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.COMPARISON:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0()) {
					sequence_Comparison(context, (Comparison) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.CONFIGURATION:
				if(context == grammarAccess.getConfigurationRule()) {
					sequence_Configuration(context, (Configuration) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.CONFIGURATIONS:
				if(context == grammarAccess.getConfigurationsRule()) {
					sequence_Configurations(context, (Configurations) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.DELTA_MODULE:
				if(context == grammarAccess.getDeltaModuleRule()) {
					sequence_DeltaModule(context, (DeltaModule) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.DELTA_PARTITION:
				if(context == grammarAccess.getDeltaPartitionRule()) {
					sequence_DeltaPartition(context, (DeltaPartition) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.EXPRESSION_STATEMENT:
				if(context == grammarAccess.getExpressionStatementRule() ||
				   context == grammarAccess.getStatementRule()) {
					sequence_ExpressionStatement(context, (ExpressionStatement) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.FEATURE:
				if(context == grammarAccess.getFeatureRule()) {
					sequence_Feature(context, (Feature) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.FEATURE_REF:
				if(context == grammarAccess.getAndRule() ||
				   context == grammarAccess.getAndAccess().getAndLeftAction_1_0() ||
				   context == grammarAccess.getPrimaryRule() ||
				   context == grammarAccess.getPropositionalFormulaRule() ||
				   context == grammarAccess.getPropositionalFormulaAccess().getOrLeftAction_1_0()) {
					sequence_Primary(context, (FeatureRef) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.FEATURES:
				if(context == grammarAccess.getFeaturesRule()) {
					sequence_Features(context, (Features) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.FIELD:
				if(context == grammarAccess.getFieldRule() ||
				   context == grammarAccess.getTypedDeclarationRule()) {
					sequence_Field(context, (Field) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.FIELD_ADDITION:
				if(context == grammarAccess.getDeltaSubActionRule() ||
				   context == grammarAccess.getFieldAdditionRule() ||
				   context == grammarAccess.getMethodOrFieldAdditionRule()) {
					sequence_FieldAddition(context, (FieldAddition) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.FIELD_REMOVAL:
				if(context == grammarAccess.getDeltaSubActionRule() ||
				   context == grammarAccess.getFieldRemovalRule()) {
					sequence_FieldRemoval(context, (FieldRemoval) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.FIELD_SELECTION:
				if(context == grammarAccess.getFieldSelectionRule() ||
				   context == grammarAccess.getMessageRule()) {
					sequence_FieldSelection(context, (FieldSelection) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.IF_STATEMENT:
				if(context == grammarAccess.getIfStatementRule() ||
				   context == grammarAccess.getStatementRule()) {
					sequence_IfStatement(context, (IfStatement) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.INT_CONSTANT:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getConstantRule() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getIntConstantRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0() ||
				   context == grammarAccess.getTerminalExpressionRule()) {
					sequence_IntConstant(context, (IntConstant) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.INT_TYPE:
				if(context == grammarAccess.getBasicTypeRule() ||
				   context == grammarAccess.getIntTypeRule() ||
				   context == grammarAccess.getTypeRule() ||
				   context == grammarAccess.getTypeForDeclarationRule() ||
				   context == grammarAccess.getTypeForMethodRule()) {
					sequence_IntType(context, (IntType) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.JAVA_VERBATIM:
				if(context == grammarAccess.getStatementRule()) {
					sequence_Statement(context, (JavaVerbatim) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.LOCAL_VARIABLE_DECLARATION:
				if(context == grammarAccess.getLocalVariableDeclarationRule() ||
				   context == grammarAccess.getTypedDeclarationRule()) {
					sequence_LocalVariableDeclaration(context, (LocalVariableDeclaration) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.METHOD:
				if(context == grammarAccess.getMethodRule()) {
					sequence_Method(context, (Method) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.METHOD_ADDITION:
				if(context == grammarAccess.getDeltaSubActionRule() ||
				   context == grammarAccess.getMethodAdditionRule() ||
				   context == grammarAccess.getMethodOrFieldAdditionRule()) {
					sequence_MethodAddition(context, (MethodAddition) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.METHOD_CALL:
				if(context == grammarAccess.getMessageRule() ||
				   context == grammarAccess.getMethodCallRule()) {
					sequence_MethodCall(context, (MethodCall) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.METHOD_MODIFICATION:
				if(context == grammarAccess.getDeltaSubActionRule() ||
				   context == grammarAccess.getMethodModificationRule()) {
					sequence_MethodModification(context, (MethodModification) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.METHOD_REMOVAL:
				if(context == grammarAccess.getDeltaSubActionRule() ||
				   context == grammarAccess.getMethodRemovalRule()) {
					sequence_MethodRemoval(context, (MethodRemoval) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.MINUS:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getExpressionRule()) {
					sequence_Addition(context, (Minus) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.MODULE_REFERENCE:
				if(context == grammarAccess.getModuleReferenceRule()) {
					sequence_ModuleReference(context, (ModuleReference) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.MULTI_OR_DIV:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0()) {
					sequence_Multiplication(context, (MultiOrDiv) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.NEGATION:
				if(context == grammarAccess.getAndRule() ||
				   context == grammarAccess.getAndAccess().getAndLeftAction_1_0() ||
				   context == grammarAccess.getPrimaryRule() ||
				   context == grammarAccess.getPropositionalFormulaRule() ||
				   context == grammarAccess.getPropositionalFormulaAccess().getOrLeftAction_1_0()) {
					sequence_Primary(context, (Negation) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.NEW:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0() ||
				   context == grammarAccess.getNewRule() ||
				   context == grammarAccess.getTerminalExpressionRule()) {
					sequence_New(context, (New) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.NULL:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0() ||
				   context == grammarAccess.getNullRule() ||
				   context == grammarAccess.getTerminalExpressionRule()) {
					sequence_Null(context, (Null) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.OR:
				if(context == grammarAccess.getPropositionalFormulaRule() ||
				   context == grammarAccess.getPropositionalFormulaAccess().getOrLeftAction_1_0()) {
					sequence_PropositionalFormula(context, (Or) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.ORIGINAL:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0() ||
				   context == grammarAccess.getOriginalRule() ||
				   context == grammarAccess.getTerminalExpressionRule()) {
					sequence_Original(context, (Original) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.PARAMETER:
				if(context == grammarAccess.getParameterRule() ||
				   context == grammarAccess.getTypedDeclarationRule()) {
					sequence_Parameter(context, (Parameter) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.PAREN:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0() ||
				   context == grammarAccess.getParenRule() ||
				   context == grammarAccess.getTerminalExpressionRule()) {
					sequence_Paren(context, (Paren) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.PARTITION_PART:
				if(context == grammarAccess.getPartitionPartRule()) {
					sequence_PartitionPart(context, (PartitionPart) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.PLUS:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getExpressionRule()) {
					sequence_Addition(context, (Plus) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.PRODUCT:
				if(context == grammarAccess.getProductRule()) {
					sequence_Product(context, (Product) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.PRODUCT_LINE:
				if(context == grammarAccess.getProductLineRule()) {
					sequence_ProductLine(context, (ProductLine) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.PROGRAM:
				if(context == grammarAccess.getProgramRule()) {
					sequence_Program(context, (Program) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.PROP_FALSE:
				if(context == grammarAccess.getAndRule() ||
				   context == grammarAccess.getAndAccess().getAndLeftAction_1_0() ||
				   context == grammarAccess.getPrimaryRule() ||
				   context == grammarAccess.getPropositionalFormulaRule() ||
				   context == grammarAccess.getPropositionalFormulaAccess().getOrLeftAction_1_0()) {
					sequence_PropositionalFormula(context, (PropFalse) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.PROP_PAREN:
				if(context == grammarAccess.getAndRule() ||
				   context == grammarAccess.getAndAccess().getAndLeftAction_1_0() ||
				   context == grammarAccess.getPrimaryRule() ||
				   context == grammarAccess.getPropositionalFormulaRule() ||
				   context == grammarAccess.getPropositionalFormulaAccess().getOrLeftAction_1_0()) {
					sequence_Primary(context, (PropParen) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.PROP_TRUE:
				if(context == grammarAccess.getAndRule() ||
				   context == grammarAccess.getAndAccess().getAndLeftAction_1_0() ||
				   context == grammarAccess.getPrimaryRule() ||
				   context == grammarAccess.getPropositionalFormulaRule() ||
				   context == grammarAccess.getPropositionalFormulaAccess().getOrLeftAction_1_0()) {
					sequence_PropositionalFormula(context, (PropTrue) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.RETURN_STATEMENT:
				if(context == grammarAccess.getReturnStatementRule()) {
					sequence_ReturnStatement(context, (ReturnStatement) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.SELECTION:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0()) {
					sequence_Atomic(context, (Selection) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.STATEMENT_BLOCK:
				if(context == grammarAccess.getStatementBlockRule()) {
					sequence_StatementBlock(context, (StatementBlock) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.STRING_CONSTANT:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getConstantRule() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0() ||
				   context == grammarAccess.getStringConstantRule() ||
				   context == grammarAccess.getTerminalExpressionRule()) {
					sequence_StringConstant(context, (StringConstant) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.STRING_TYPE:
				if(context == grammarAccess.getBasicTypeRule() ||
				   context == grammarAccess.getStringTypeRule() ||
				   context == grammarAccess.getTypeRule() ||
				   context == grammarAccess.getTypeForDeclarationRule() ||
				   context == grammarAccess.getTypeForMethodRule()) {
					sequence_StringType(context, (StringType) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.THIS:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0() ||
				   context == grammarAccess.getTerminalExpressionRule() ||
				   context == grammarAccess.getThisRule()) {
					sequence_This(context, (This) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.TYPE_VARIABLE:
				if(context == grammarAccess.getTypeRule() ||
				   context == grammarAccess.getTypeVariableRule()) {
					sequence_TypeVariable(context, (TypeVariable) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.VARIABLE_ACCESS:
				if(context == grammarAccess.getAdditionRule() ||
				   context == grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0() ||
				   context == grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0() ||
				   context == grammarAccess.getAtomicRule() ||
				   context == grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0() ||
				   context == grammarAccess.getBooleanExpressionRule() ||
				   context == grammarAccess.getBooleanExpressionAccess().getAndOrExpressionLeftAction_1_0() ||
				   context == grammarAccess.getComparisonRule() ||
				   context == grammarAccess.getComparisonAccess().getComparisonLeftAction_1_0() ||
				   context == grammarAccess.getExpressionRule() ||
				   context == grammarAccess.getMultiplicationRule() ||
				   context == grammarAccess.getMultiplicationAccess().getMultiOrDivLeftAction_1_0() ||
				   context == grammarAccess.getTerminalExpressionRule() ||
				   context == grammarAccess.getVariableAccessRule()) {
					sequence_VariableAccess(context, (VariableAccess) semanticObject); 
					return; 
				}
				else break;
			case DeltajPackage.VOID_TYPE:
				if(context == grammarAccess.getTypeRule() ||
				   context == grammarAccess.getTypeForMethodRule() ||
				   context == grammarAccess.getVoidTypeRule()) {
					sequence_VoidType(context, (VoidType) semanticObject); 
					return; 
				}
				else break;
			}
		if (errorAcceptor != null) errorAcceptor.accept(diagnosticProvider.createInvalidContextOrTypeDiagnostic(semanticObject, context));
	}
	
	/**
	 * Constraint:
	 *     (left=Addition_Minus_1_0_1_0 right=Multiplication)
	 */
	protected void sequence_Addition(EObject context, Minus semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.MINUS__LEFT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.MINUS__LEFT));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.MINUS__RIGHT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.MINUS__RIGHT));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getAdditionAccess().getMinusLeftAction_1_0_1_0(), semanticObject.getLeft());
		feeder.accept(grammarAccess.getAdditionAccess().getRightMultiplicationParserRuleCall_1_1_0(), semanticObject.getRight());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (left=Addition_Plus_1_0_0_0 right=Multiplication)
	 */
	protected void sequence_Addition(EObject context, Plus semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.PLUS__LEFT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.PLUS__LEFT));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.PLUS__RIGHT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.PLUS__RIGHT));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getAdditionAccess().getPlusLeftAction_1_0_0_0(), semanticObject.getLeft());
		feeder.accept(grammarAccess.getAdditionAccess().getRightMultiplicationParserRuleCall_1_1_0(), semanticObject.getRight());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (left=And_And_1_0 right=Primary)
	 */
	protected void sequence_And(EObject context, And semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.AND__LEFT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.AND__LEFT));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.AND__RIGHT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.AND__RIGHT));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getAndAccess().getAndLeftAction_1_0(), semanticObject.getLeft());
		feeder.accept(grammarAccess.getAndAccess().getRightPrimaryParserRuleCall_1_2_0(), semanticObject.getRight());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (left=Expression right=Expression)
	 */
	protected void sequence_Assignment(EObject context, Assignment semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.ASSIGNMENT__LEFT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.ASSIGNMENT__LEFT));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.ASSIGNMENT__RIGHT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.ASSIGNMENT__RIGHT));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getAssignmentAccess().getLeftExpressionParserRuleCall_0_0(), semanticObject.getLeft());
		feeder.accept(grammarAccess.getAssignmentAccess().getRightExpressionParserRuleCall_2_0(), semanticObject.getRight());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     expression=Atomic
	 */
	protected void sequence_Atomic(EObject context, ArithmeticSigned semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.ARITHMETIC_SIGNED__EXPRESSION) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.ARITHMETIC_SIGNED__EXPRESSION));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getAtomicAccess().getExpressionAtomicParserRuleCall_1_2_0(), semanticObject.getExpression());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     expression=Atomic
	 */
	protected void sequence_Atomic(EObject context, BooleanNegation semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.BOOLEAN_NEGATION__EXPRESSION) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.BOOLEAN_NEGATION__EXPRESSION));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getAtomicAccess().getExpressionAtomicParserRuleCall_0_2_0(), semanticObject.getExpression());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (receiver=Atomic_Selection_2_1_0 message=Message)
	 */
	protected void sequence_Atomic(EObject context, Selection semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.SELECTION__RECEIVER) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.SELECTION__RECEIVER));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.SELECTION__MESSAGE) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.SELECTION__MESSAGE));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getAtomicAccess().getSelectionReceiverAction_2_1_0(), semanticObject.getReceiver());
		feeder.accept(grammarAccess.getAtomicAccess().getMessageMessageParserRuleCall_2_1_2_0(), semanticObject.getMessage());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (constant='true' | constant='false')
	 */
	protected void sequence_BoolConstant(EObject context, BoolConstant semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     (left=BooleanExpression_AndOrExpression_1_0 (op='||' | op='&&') right=Atomic)
	 */
	protected void sequence_BooleanExpression(EObject context, AndOrExpression semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     basic='boolean'
	 */
	protected void sequence_BooleanType(EObject context, BooleanType semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.BASIC_TYPE__BASIC) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.BASIC_TYPE__BASIC));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getBooleanTypeAccess().getBasicBooleanKeyword_0(), semanticObject.getBasic());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (type=ClassName object=TerminalExpression)
	 */
	protected void sequence_Cast(EObject context, Cast semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.CAST__TYPE) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.CAST__TYPE));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.CAST__OBJECT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.CAST__OBJECT));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getCastAccess().getTypeClassNameParserRuleCall_1_0(), semanticObject.getType());
		feeder.accept(grammarAccess.getCastAccess().getObjectTerminalExpressionParserRuleCall_3_0(), semanticObject.getObject());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     class=Class
	 */
	protected void sequence_ClassAddition(EObject context, ClassAddition semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.CLASS_ADDITION__CLASS) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.CLASS_ADDITION__CLASS));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getClassAdditionAccess().getClassClassParserRuleCall_1_0(), semanticObject.getClass_());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (name=ClassName extends=ClassName? subActions+=DeltaSubAction*)
	 */
	protected void sequence_ClassModification(EObject context, ClassModification semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     name=ClassName
	 */
	protected void sequence_ClassRemoval(EObject context, ClassRemoval semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.REMOVES_OR_MODIFIES_CLASS__NAME) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.REMOVES_OR_MODIFIES_CLASS__NAME));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getClassRemovalAccess().getNameClassNameParserRuleCall_1_0(), semanticObject.getName());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     classref=ClassName
	 */
	protected void sequence_ClassType(EObject context, ClassType semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.CLASS_TYPE__CLASSREF) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.CLASS_TYPE__CLASSREF));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getClassTypeAccess().getClassrefClassNameParserRuleCall_0(), semanticObject.getClassref());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (name=ID extends=ClassName? fields+=Field* methods+=Method*)
	 */
	protected void sequence_Class(EObject context, org.deltaj.deltaj.Class semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     (
	 *         left=Comparison_Comparison_1_0 
	 *         (
	 *             op='>=' | 
	 *             op='<=' | 
	 *             op='<' | 
	 *             op='>' | 
	 *             op='==' | 
	 *             op='!='
	 *         ) 
	 *         right=BooleanExpression
	 *     )
	 */
	protected void sequence_Comparison(EObject context, Comparison semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     formula=PropositionalFormula
	 */
	protected void sequence_Configuration(EObject context, Configuration semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.CONFIGURATION__FORMULA) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.CONFIGURATION__FORMULA));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getConfigurationAccess().getFormulaPropositionalFormulaParserRuleCall_0(), semanticObject.getFormula());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (configurations+=Configuration configurations+=Configuration*)
	 */
	protected void sequence_Configurations(EObject context, Configurations semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     (name=ID deltaActions+=DeltaAction*)
	 */
	protected void sequence_DeltaModule(EObject context, DeltaModule semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     parts+=PartitionPart+
	 */
	protected void sequence_DeltaPartition(EObject context, DeltaPartition semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     expression=Expression
	 */
	protected void sequence_ExpressionStatement(EObject context, ExpressionStatement semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.EXPRESSION_STATEMENT__EXPRESSION) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.EXPRESSION_STATEMENT__EXPRESSION));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getExpressionStatementAccess().getExpressionExpressionParserRuleCall_0_0(), semanticObject.getExpression());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     name=ID
	 */
	protected void sequence_Feature(EObject context, Feature semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.FEATURE__NAME) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.FEATURE__NAME));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getFeatureAccess().getNameIDTerminalRuleCall_0(), semanticObject.getName());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (featuresList+=Feature featuresList+=Feature*)
	 */
	protected void sequence_Features(EObject context, Features semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     field=Field
	 */
	protected void sequence_FieldAddition(EObject context, FieldAddition semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.FIELD_ADDITION__FIELD) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.FIELD_ADDITION__FIELD));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getFieldAdditionAccess().getFieldFieldParserRuleCall_1_0(), semanticObject.getField());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     name=FieldName
	 */
	protected void sequence_FieldRemoval(EObject context, FieldRemoval semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.FIELD_REMOVAL__NAME) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.FIELD_REMOVAL__NAME));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getFieldRemovalAccess().getNameFieldNameParserRuleCall_1_0(), semanticObject.getName());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     field=ID
	 */
	protected void sequence_FieldSelection(EObject context, FieldSelection semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.FIELD_SELECTION__FIELD) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.FIELD_SELECTION__FIELD));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getFieldSelectionAccess().getFieldIDTerminalRuleCall_0(), semanticObject.getField());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (type=TypeForDeclaration name=ID)
	 */
	protected void sequence_Field(EObject context, Field semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.TYPED_DECLARATION__TYPE) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.TYPED_DECLARATION__TYPE));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.TYPED_DECLARATION__NAME) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.TYPED_DECLARATION__NAME));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getFieldAccess().getTypeTypeForDeclarationParserRuleCall_0_0(), semanticObject.getType());
		feeder.accept(grammarAccess.getFieldAccess().getNameIDTerminalRuleCall_1_0(), semanticObject.getName());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (expression=Expression thenBlock=StatementBlock elseBlock=StatementBlock?)
	 */
	protected void sequence_IfStatement(EObject context, IfStatement semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     constant=INT
	 */
	protected void sequence_IntConstant(EObject context, IntConstant semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.INT_CONSTANT__CONSTANT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.INT_CONSTANT__CONSTANT));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getIntConstantAccess().getConstantINTTerminalRuleCall_0(), semanticObject.getConstant());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     basic='int'
	 */
	protected void sequence_IntType(EObject context, IntType semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.BASIC_TYPE__BASIC) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.BASIC_TYPE__BASIC));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getIntTypeAccess().getBasicIntKeyword_0(), semanticObject.getBasic());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (type=TypeForDeclaration name=ID)
	 */
	protected void sequence_LocalVariableDeclaration(EObject context, LocalVariableDeclaration semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.TYPED_DECLARATION__TYPE) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.TYPED_DECLARATION__TYPE));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.TYPED_DECLARATION__NAME) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.TYPED_DECLARATION__NAME));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getLocalVariableDeclarationAccess().getTypeTypeForDeclarationParserRuleCall_0_0(), semanticObject.getType());
		feeder.accept(grammarAccess.getLocalVariableDeclarationAccess().getNameIDTerminalRuleCall_1_0(), semanticObject.getName());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     method=Method
	 */
	protected void sequence_MethodAddition(EObject context, MethodAddition semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.METHOD_ADDITION__METHOD) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.METHOD_ADDITION__METHOD));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getMethodAdditionAccess().getMethodMethodParserRuleCall_1_0(), semanticObject.getMethod());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (method=ID (args+=Expression args+=Expression*)?)
	 */
	protected void sequence_MethodCall(EObject context, MethodCall semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     method=Method
	 */
	protected void sequence_MethodModification(EObject context, MethodModification semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.METHOD_MODIFICATION__METHOD) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.METHOD_MODIFICATION__METHOD));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getMethodModificationAccess().getMethodMethodParserRuleCall_1_0(), semanticObject.getMethod());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     name=MethodName
	 */
	protected void sequence_MethodRemoval(EObject context, MethodRemoval semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.METHOD_REMOVAL__NAME) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.METHOD_REMOVAL__NAME));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getMethodRemovalAccess().getNameMethodNameParserRuleCall_1_0(), semanticObject.getName());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (returntype=TypeForMethod name=ID (params+=Parameter params+=Parameter*)? body=StatementBlock?)
	 */
	protected void sequence_Method(EObject context, Method semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     (deltaModule=[DeltaModule|ID] when=PropositionalFormula?)
	 */
	protected void sequence_ModuleReference(EObject context, ModuleReference semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     (left=Multiplication_MultiOrDiv_1_0 (op='*' | op='/') right=Comparison)
	 */
	protected void sequence_Multiplication(EObject context, MultiOrDiv semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     class=ClassName
	 */
	protected void sequence_New(EObject context, New semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.NEW__CLASS) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.NEW__CLASS));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getNewAccess().getClassClassNameParserRuleCall_1_0(), semanticObject.getClass_());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     null='null'
	 */
	protected void sequence_Null(EObject context, Null semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.NULL__NULL) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.NULL__NULL));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getNullAccess().getNullNullKeyword_0(), semanticObject.getNull());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (method='original' (args+=Expression args+=Expression*)?)
	 */
	protected void sequence_Original(EObject context, Original semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     (type=TypeForDeclaration name=ID)
	 */
	protected void sequence_Parameter(EObject context, Parameter semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.TYPED_DECLARATION__TYPE) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.TYPED_DECLARATION__TYPE));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.TYPED_DECLARATION__NAME) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.TYPED_DECLARATION__NAME));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getParameterAccess().getTypeTypeForDeclarationParserRuleCall_0_0(), semanticObject.getType());
		feeder.accept(grammarAccess.getParameterAccess().getNameIDTerminalRuleCall_1_0(), semanticObject.getName());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     expression=Expression
	 */
	protected void sequence_Paren(EObject context, Paren semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.PAREN__EXPRESSION) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.PAREN__EXPRESSION));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getParenAccess().getExpressionExpressionParserRuleCall_1_0(), semanticObject.getExpression());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (moduleReferences+=ModuleReference moduleReferences+=ModuleReference*)
	 */
	protected void sequence_PartitionPart(EObject context, PartitionPart semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     feature=[Feature|ID]
	 */
	protected void sequence_Primary(EObject context, FeatureRef semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.FEATURE_REF__FEATURE) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.FEATURE_REF__FEATURE));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getPrimaryAccess().getFeatureFeatureIDTerminalRuleCall_0_1_0_1(), semanticObject.getFeature());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     formula=Primary
	 */
	protected void sequence_Primary(EObject context, Negation semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.NEGATION__FORMULA) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.NEGATION__FORMULA));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getPrimaryAccess().getFormulaPrimaryParserRuleCall_2_2_0(), semanticObject.getFormula());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     formula=PropositionalFormula
	 */
	protected void sequence_Primary(EObject context, PropParen semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.PROP_PAREN__FORMULA) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.PROP_PAREN__FORMULA));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getPrimaryAccess().getFormulaPropositionalFormulaParserRuleCall_1_2_0(), semanticObject.getFormula());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (name=ID features=Features configurations=Configurations partition=DeltaPartition)
	 */
	protected void sequence_ProductLine(EObject context, ProductLine semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.PRODUCT_LINE__NAME) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.PRODUCT_LINE__NAME));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.PRODUCT_LINE__FEATURES) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.PRODUCT_LINE__FEATURES));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.PRODUCT_LINE__CONFIGURATIONS) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.PRODUCT_LINE__CONFIGURATIONS));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.PRODUCT_LINE__PARTITION) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.PRODUCT_LINE__PARTITION));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getProductLineAccess().getNameIDTerminalRuleCall_1_0(), semanticObject.getName());
		feeder.accept(grammarAccess.getProductLineAccess().getFeaturesFeaturesParserRuleCall_3_0(), semanticObject.getFeatures());
		feeder.accept(grammarAccess.getProductLineAccess().getConfigurationsConfigurationsParserRuleCall_4_0(), semanticObject.getConfigurations());
		feeder.accept(grammarAccess.getProductLineAccess().getPartitionDeltaPartitionParserRuleCall_5_0(), semanticObject.getPartition());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     (name=ID productLine=[ProductLine|ID] features+=[Feature|ID] features+=[Feature|ID]*)
	 */
	protected void sequence_Product(EObject context, Product semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     (deltaModules+=DeltaModule* productLines+=ProductLine* products+=Product*)
	 */
	protected void sequence_Program(EObject context, Program semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     (left=PropositionalFormula_Or_1_0 right=And)
	 */
	protected void sequence_PropositionalFormula(EObject context, Or semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.OR__LEFT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.OR__LEFT));
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.OR__RIGHT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.OR__RIGHT));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getPropositionalFormulaAccess().getOrLeftAction_1_0(), semanticObject.getLeft());
		feeder.accept(grammarAccess.getPropositionalFormulaAccess().getRightAndParserRuleCall_1_2_0(), semanticObject.getRight());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     {PropFalse}
	 */
	protected void sequence_PropositionalFormula(EObject context, PropFalse semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     {PropTrue}
	 */
	protected void sequence_PropositionalFormula(EObject context, PropTrue semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     (expression=Expression?)
	 */
	protected void sequence_ReturnStatement(EObject context, ReturnStatement semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     (localvariables+=LocalVariableDeclaration* statements+=Statement* statements+=ReturnStatement?)
	 */
	protected void sequence_StatementBlock(EObject context, StatementBlock semanticObject) {
		genericSequencer.createSequence(context, semanticObject);
	}
	
	
	/**
	 * Constraint:
	 *     verbatim=JAVAVERBATIM
	 */
	protected void sequence_Statement(EObject context, JavaVerbatim semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.JAVA_VERBATIM__VERBATIM) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.JAVA_VERBATIM__VERBATIM));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getStatementAccess().getVerbatimJAVAVERBATIMTerminalRuleCall_3_1_0(), semanticObject.getVerbatim());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     constant=STRING
	 */
	protected void sequence_StringConstant(EObject context, StringConstant semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.STRING_CONSTANT__CONSTANT) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.STRING_CONSTANT__CONSTANT));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getStringConstantAccess().getConstantSTRINGTerminalRuleCall_0(), semanticObject.getConstant());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     basic='String'
	 */
	protected void sequence_StringType(EObject context, StringType semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.BASIC_TYPE__BASIC) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.BASIC_TYPE__BASIC));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getStringTypeAccess().getBasicStringKeyword_0(), semanticObject.getBasic());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     variable='this'
	 */
	protected void sequence_This(EObject context, This semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.THIS__VARIABLE) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.THIS__VARIABLE));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getThisAccess().getVariableThisKeyword_0(), semanticObject.getVariable());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     varName=TypeVariableId
	 */
	protected void sequence_TypeVariable(EObject context, TypeVariable semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.TYPE_VARIABLE__VAR_NAME) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.TYPE_VARIABLE__VAR_NAME));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getTypeVariableAccess().getVarNameTypeVariableIdParserRuleCall_0(), semanticObject.getVarName());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     variable=[TypedDeclaration|ID]
	 */
	protected void sequence_VariableAccess(EObject context, VariableAccess semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.VARIABLE_ACCESS__VARIABLE) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.VARIABLE_ACCESS__VARIABLE));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getVariableAccessAccess().getVariableTypedDeclarationIDTerminalRuleCall_0_1(), semanticObject.getVariable());
		feeder.finish();
	}
	
	
	/**
	 * Constraint:
	 *     void='void'
	 */
	protected void sequence_VoidType(EObject context, VoidType semanticObject) {
		if(errorAcceptor != null) {
			if(transientValues.isValueTransient(semanticObject, DeltajPackage.Literals.VOID_TYPE__VOID) == ValueTransient.YES)
				errorAcceptor.accept(diagnosticProvider.createFeatureValueMissing(semanticObject, DeltajPackage.Literals.VOID_TYPE__VOID));
		}
		INodesForEObjectProvider nodes = createNodeProvider(semanticObject);
		SequenceFeeder feeder = createSequencerFeeder(semanticObject, nodes);
		feeder.accept(grammarAccess.getVoidTypeAccess().getVoidVoidKeyword_0(), semanticObject.getVoid());
		feeder.finish();
	}
}
