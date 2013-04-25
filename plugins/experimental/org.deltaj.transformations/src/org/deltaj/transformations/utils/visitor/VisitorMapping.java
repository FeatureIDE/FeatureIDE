package org.deltaj.transformations.utils.visitor;

class VisitorMapping<Result, Parameter> {

	private final Class<Parameter> parameterClass;
	private final IVisitor<Result, Parameter> visitor;

	public VisitorMapping(Class<Parameter> parameterClass, IVisitor<Result, Parameter> visitor) {

		this.parameterClass = parameterClass;
		this.visitor = visitor;
	}

	public Result visit(Object parameter) {

		return this.visitor.visit(this.parameterClass.cast(parameter));
	}
}
