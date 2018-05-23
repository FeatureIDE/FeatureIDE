package org.deltaj.transformations.utils.visitor;

import java.util.Map;
import org.deltaj.transformations.utils.MapFactory;

public class VisitorDispatcher<Result> {

	private final Map<Class<?>, VisitorMapping<Result, ?>> visitorMappings;

	public VisitorDispatcher() {

		this.visitorMappings = MapFactory.createIdentityHashMap();
	}

	public <Parameter> void add(Class<Parameter> parameterClass, IVisitor<Result, Parameter> visitor) {

		this.visitorMappings.put(parameterClass, new VisitorMapping<Result, Parameter>(parameterClass, visitor));
	}

	public Result visit(Object parameter) {

		Class<?> parameterClass = parameter.getClass();

		VisitorMapping<Result, ?> mapping = this.findMapping(parameterClass);

		if (mapping != null) {
			return mapping.visit(parameter);
		} else {
			throw new RuntimeException(String.format("Could not find a visitor mapping for parameter class '%s'.", parameter.getClass().getCanonicalName()));
		}
	}

	private VisitorMapping<Result, ?> findMapping(Class<?> parameterClass) {

		VisitorMapping<Result, ?> mapping = this.visitorMappings.get(parameterClass);
		if (mapping != null) {
			return mapping;
		}

		mapping = this.findMappingForInterfaces(parameterClass);
		if (mapping != null) {
			return mapping;
		}

		return this.findMapping(parameterClass.getSuperclass());
	}

	private VisitorMapping<Result, ?> findMappingForInterfaces(Class<?> parameterClass) {

		for (Class<?> parameterInterface: parameterClass.getInterfaces()) {

			VisitorMapping<Result, ?> mapping = this.findMapping(parameterInterface);
			if (mapping != null) {
				return mapping;
			}
		}

		return null;
	}
}
