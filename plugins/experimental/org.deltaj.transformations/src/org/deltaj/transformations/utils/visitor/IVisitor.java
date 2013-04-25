package org.deltaj.transformations.utils.visitor;

/**
 * Generic interface of a visitor for the visitor pattern.
 * 
 * @author Oliver Richers
 * 
 * @param <Result>
 *            the type of the visitor result
 * @param <Parameter>
 *            the type of the parameter to the visitor
 */
public interface IVisitor<Result, Parameter> {

	Result visit(Parameter object);
}
