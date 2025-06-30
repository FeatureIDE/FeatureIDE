// Generated from Velvet.g4 by ANTLR 4.13.2

package de.ovgu.featureide.fm.core.io.velvet;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link VelvetParser}.
 */
public interface VelvetListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link VelvetParser#velvetModel}.
	 * @param ctx the parse tree
	 */
	void enterVelvetModel(VelvetParser.VelvetModelContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#velvetModel}.
	 * @param ctx the parse tree
	 */
	void exitVelvetModel(VelvetParser.VelvetModelContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#imp}.
	 * @param ctx the parse tree
	 */
	void enterImp(VelvetParser.ImpContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#imp}.
	 * @param ctx the parse tree
	 */
	void exitImp(VelvetParser.ImpContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#concept}.
	 * @param ctx the parse tree
	 */
	void enterConcept(VelvetParser.ConceptContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#concept}.
	 * @param ctx the parse tree
	 */
	void exitConcept(VelvetParser.ConceptContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#cinterface}.
	 * @param ctx the parse tree
	 */
	void enterCinterface(VelvetParser.CinterfaceContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#cinterface}.
	 * @param ctx the parse tree
	 */
	void exitCinterface(VelvetParser.CinterfaceContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#conceptBaseExt}.
	 * @param ctx the parse tree
	 */
	void enterConceptBaseExt(VelvetParser.ConceptBaseExtContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#conceptBaseExt}.
	 * @param ctx the parse tree
	 */
	void exitConceptBaseExt(VelvetParser.ConceptBaseExtContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#instanceImports}.
	 * @param ctx the parse tree
	 */
	void enterInstanceImports(VelvetParser.InstanceImportsContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#instanceImports}.
	 * @param ctx the parse tree
	 */
	void exitInstanceImports(VelvetParser.InstanceImportsContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#interfaceImports}.
	 * @param ctx the parse tree
	 */
	void enterInterfaceImports(VelvetParser.InterfaceImportsContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#interfaceImports}.
	 * @param ctx the parse tree
	 */
	void exitInterfaceImports(VelvetParser.InterfaceImportsContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#name}.
	 * @param ctx the parse tree
	 */
	void enterName(VelvetParser.NameContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#name}.
	 * @param ctx the parse tree
	 */
	void exitName(VelvetParser.NameContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#definitions}.
	 * @param ctx the parse tree
	 */
	void enterDefinitions(VelvetParser.DefinitionsContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#definitions}.
	 * @param ctx the parse tree
	 */
	void exitDefinitions(VelvetParser.DefinitionsContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#definition}.
	 * @param ctx the parse tree
	 */
	void enterDefinition(VelvetParser.DefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#definition}.
	 * @param ctx the parse tree
	 */
	void exitDefinition(VelvetParser.DefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#nonFeatureDefinition}.
	 * @param ctx the parse tree
	 */
	void enterNonFeatureDefinition(VelvetParser.NonFeatureDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#nonFeatureDefinition}.
	 * @param ctx the parse tree
	 */
	void exitNonFeatureDefinition(VelvetParser.NonFeatureDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#use}.
	 * @param ctx the parse tree
	 */
	void enterUse(VelvetParser.UseContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#use}.
	 * @param ctx the parse tree
	 */
	void exitUse(VelvetParser.UseContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#feature}.
	 * @param ctx the parse tree
	 */
	void enterFeature(VelvetParser.FeatureContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#feature}.
	 * @param ctx the parse tree
	 */
	void exitFeature(VelvetParser.FeatureContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#featureGroup}.
	 * @param ctx the parse tree
	 */
	void enterFeatureGroup(VelvetParser.FeatureGroupContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#featureGroup}.
	 * @param ctx the parse tree
	 */
	void exitFeatureGroup(VelvetParser.FeatureGroupContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#groupType}.
	 * @param ctx the parse tree
	 */
	void enterGroupType(VelvetParser.GroupTypeContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#groupType}.
	 * @param ctx the parse tree
	 */
	void exitGroupType(VelvetParser.GroupTypeContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#description}.
	 * @param ctx the parse tree
	 */
	void enterDescription(VelvetParser.DescriptionContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#description}.
	 * @param ctx the parse tree
	 */
	void exitDescription(VelvetParser.DescriptionContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#constraint}.
	 * @param ctx the parse tree
	 */
	void enterConstraint(VelvetParser.ConstraintContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#constraint}.
	 * @param ctx the parse tree
	 */
	void exitConstraint(VelvetParser.ConstraintContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#constraintDefinition}.
	 * @param ctx the parse tree
	 */
	void enterConstraintDefinition(VelvetParser.ConstraintDefinitionContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#constraintDefinition}.
	 * @param ctx the parse tree
	 */
	void exitConstraintDefinition(VelvetParser.ConstraintDefinitionContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#constraintOperand}.
	 * @param ctx the parse tree
	 */
	void enterConstraintOperand(VelvetParser.ConstraintOperandContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#constraintOperand}.
	 * @param ctx the parse tree
	 */
	void exitConstraintOperand(VelvetParser.ConstraintOperandContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#attribute}.
	 * @param ctx the parse tree
	 */
	void enterAttribute(VelvetParser.AttributeContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#attribute}.
	 * @param ctx the parse tree
	 */
	void exitAttribute(VelvetParser.AttributeContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#attributeConstraint}.
	 * @param ctx the parse tree
	 */
	void enterAttributeConstraint(VelvetParser.AttributeConstraintContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#attributeConstraint}.
	 * @param ctx the parse tree
	 */
	void exitAttributeConstraint(VelvetParser.AttributeConstraintContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#attribConstraint}.
	 * @param ctx the parse tree
	 */
	void enterAttribConstraint(VelvetParser.AttribConstraintContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#attribConstraint}.
	 * @param ctx the parse tree
	 */
	void exitAttribConstraint(VelvetParser.AttribConstraintContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#attribOperator}.
	 * @param ctx the parse tree
	 */
	void enterAttribOperator(VelvetParser.AttribOperatorContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#attribOperator}.
	 * @param ctx the parse tree
	 */
	void exitAttribOperator(VelvetParser.AttribOperatorContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#attribNumInstance}.
	 * @param ctx the parse tree
	 */
	void enterAttribNumInstance(VelvetParser.AttribNumInstanceContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#attribNumInstance}.
	 * @param ctx the parse tree
	 */
	void exitAttribNumInstance(VelvetParser.AttribNumInstanceContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#intAttribute}.
	 * @param ctx the parse tree
	 */
	void enterIntAttribute(VelvetParser.IntAttributeContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#intAttribute}.
	 * @param ctx the parse tree
	 */
	void exitIntAttribute(VelvetParser.IntAttributeContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#floatAttribute}.
	 * @param ctx the parse tree
	 */
	void enterFloatAttribute(VelvetParser.FloatAttributeContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#floatAttribute}.
	 * @param ctx the parse tree
	 */
	void exitFloatAttribute(VelvetParser.FloatAttributeContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#stringAttribute}.
	 * @param ctx the parse tree
	 */
	void enterStringAttribute(VelvetParser.StringAttributeContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#stringAttribute}.
	 * @param ctx the parse tree
	 */
	void exitStringAttribute(VelvetParser.StringAttributeContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#boolAttribute}.
	 * @param ctx the parse tree
	 */
	void enterBoolAttribute(VelvetParser.BoolAttributeContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#boolAttribute}.
	 * @param ctx the parse tree
	 */
	void exitBoolAttribute(VelvetParser.BoolAttributeContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#unaryOp}.
	 * @param ctx the parse tree
	 */
	void enterUnaryOp(VelvetParser.UnaryOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#unaryOp}.
	 * @param ctx the parse tree
	 */
	void exitUnaryOp(VelvetParser.UnaryOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#binaryOp}.
	 * @param ctx the parse tree
	 */
	void enterBinaryOp(VelvetParser.BinaryOpContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#binaryOp}.
	 * @param ctx the parse tree
	 */
	void exitBinaryOp(VelvetParser.BinaryOpContext ctx);
	/**
	 * Enter a parse tree produced by {@link VelvetParser#attribRelation}.
	 * @param ctx the parse tree
	 */
	void enterAttribRelation(VelvetParser.AttribRelationContext ctx);
	/**
	 * Exit a parse tree produced by {@link VelvetParser#attribRelation}.
	 * @param ctx the parse tree
	 */
	void exitAttribRelation(VelvetParser.AttribRelationContext ctx);
}