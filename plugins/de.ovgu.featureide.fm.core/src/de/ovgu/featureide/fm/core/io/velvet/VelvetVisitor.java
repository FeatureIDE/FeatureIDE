// Generated from Velvet.g4 by ANTLR 4.13.2

package de.ovgu.featureide.fm.core.io.velvet;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link VelvetParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface VelvetVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link VelvetParser#velvetModel}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitVelvetModel(VelvetParser.VelvetModelContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#imp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitImp(VelvetParser.ImpContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#concept}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConcept(VelvetParser.ConceptContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#cinterface}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCinterface(VelvetParser.CinterfaceContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#conceptBaseExt}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConceptBaseExt(VelvetParser.ConceptBaseExtContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#instanceImports}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInstanceImports(VelvetParser.InstanceImportsContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#interfaceImports}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInterfaceImports(VelvetParser.InterfaceImportsContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#name}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitName(VelvetParser.NameContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#definitions}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDefinitions(VelvetParser.DefinitionsContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#definition}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDefinition(VelvetParser.DefinitionContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#nonFeatureDefinition}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitNonFeatureDefinition(VelvetParser.NonFeatureDefinitionContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#use}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUse(VelvetParser.UseContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#feature}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFeature(VelvetParser.FeatureContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#featureGroup}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFeatureGroup(VelvetParser.FeatureGroupContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#groupType}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitGroupType(VelvetParser.GroupTypeContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#description}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitDescription(VelvetParser.DescriptionContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#constraint}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConstraint(VelvetParser.ConstraintContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#constraintDefinition}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConstraintDefinition(VelvetParser.ConstraintDefinitionContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#constraintOperand}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitConstraintOperand(VelvetParser.ConstraintOperandContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#attribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttribute(VelvetParser.AttributeContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#attributeConstraint}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttributeConstraint(VelvetParser.AttributeConstraintContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#attribNumExpr}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttribNumExpr(VelvetParser.AttribNumExprContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#attribOperator}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttribOperator(VelvetParser.AttribOperatorContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#attribNumInstance}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttribNumInstance(VelvetParser.AttribNumInstanceContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#intAttribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitIntAttribute(VelvetParser.IntAttributeContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#floatAttribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitFloatAttribute(VelvetParser.FloatAttributeContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#stringAttribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStringAttribute(VelvetParser.StringAttributeContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#boolAttribute}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBoolAttribute(VelvetParser.BoolAttributeContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#unaryOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitUnaryOp(VelvetParser.UnaryOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#binaryOp}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitBinaryOp(VelvetParser.BinaryOpContext ctx);
	/**
	 * Visit a parse tree produced by {@link VelvetParser#attribRelation}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitAttribRelation(VelvetParser.AttribRelationContext ctx);
}