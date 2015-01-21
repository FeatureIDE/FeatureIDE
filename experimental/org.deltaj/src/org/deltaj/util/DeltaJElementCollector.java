/**
 * 
 */
package org.deltaj.util;

import java.util.Collection;
import java.util.LinkedList;
import java.util.TreeSet;

import org.deltaj.deltaj.DeltajPackage;
import org.deltaj.deltaj.Method;
import org.eclipse.emf.ecore.EClass;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.naming.IQualifiedNameProvider;
import org.eclipse.xtext.naming.QualifiedName;
import org.eclipse.xtext.resource.IContainer;
import org.eclipse.xtext.resource.IEObjectDescription;
import org.eclipse.xtext.resource.IResourceDescription;
import org.eclipse.xtext.resource.IResourceDescriptions;
import org.eclipse.xtext.resource.impl.ResourceDescriptionsProvider;

import com.google.common.base.Function;
import com.google.common.base.Predicate;
import com.google.common.collect.Collections2;
import com.google.common.collect.Lists;
import com.google.inject.Inject;

/**
 * @author bettini
 * 
 */
public class DeltaJElementCollector {

	protected static class SimpleNameCollector implements
			Function<IEObjectDescription, String> {
		@Override
		public String apply(IEObjectDescription from) {
			return from.getName().getLastSegment();
		}
	}

	protected static class QualifiedNameCollector implements
			Function<IEObjectDescription, QualifiedName> {
		@Override
		public QualifiedName apply(IEObjectDescription from) {
			return from.getName();
		}
	}

	@Inject
	protected ResourceDescriptionsProvider resourceDescriptionsProvider;

	@Inject
	protected IContainer.Manager manager;

	@Inject
	protected IQualifiedNameProvider nameProvider;

	public Collection<String> getAllAvailableClassNames(EObject context) {
		return getAvailableNamesByType(context, DeltajPackage.Literals.CLASS);
	}

	public Collection<String> getAllAvailableFieldNames(EObject context) {
		return getAvailableNamesByType(context, DeltajPackage.Literals.FIELD);
	}

	public Collection<String> getAllAvailableMethodNames(EObject context) {
		return getAvailableNamesByType(context, DeltajPackage.Literals.METHOD);
	}

	/**
	 * Searches for methods in the whole available resources with the same of
	 * the specified one but with different qualified name.
	 * 
	 * @param method
	 * @return
	 */
	public Collection<QualifiedName> getMethodsWithTheSameName(
			final Method method) {
		Collection<QualifiedName> methods = getAvailableQualifiedNamesByType(
				method, DeltajPackage.Literals.METHOD);
		final QualifiedName fullyQualifiedName = nameProvider
				.getFullyQualifiedName(method);

		return Collections2.filter(methods, new Predicate<QualifiedName>() {

			@Override
			public boolean apply(QualifiedName input) {
				return !fullyQualifiedName
						.equals(input)
						&& method.getName().equals(input.getLastSegment());
			}
		});
	}

	public Collection<String> getAvailableNamesByType(EObject context,
			EClass type) {
		return new TreeSet<String>(Collections2.transform(
				getAllVisibleObjectsByType(context, type),
				new SimpleNameCollector()));
	}

	public Collection<QualifiedName> getAvailableQualifiedNamesByType(
			EObject context, EClass type) {
		return Collections2.transform(
				getAllVisibleObjectsByType(context, type),
				new QualifiedNameCollector());
	}

	public Collection<IEObjectDescription> getAllAvailableClasses(
			EObject context) {
		return getAllVisibleObjectsByType(context, DeltajPackage.Literals.CLASS);
	}

	protected Collection<IEObjectDescription> getAllVisibleObjectsByType(
			EObject context, EClass type) {
		Resource eResource = context.eResource();
		IResourceDescriptions index = resourceDescriptionsProvider
				.getResourceDescriptions(eResource);
		IResourceDescription resourceDescription = index
				.getResourceDescription(eResource.getURI());
		Collection<IEObjectDescription> classDescriptions = new LinkedList<IEObjectDescription>();
		for (IContainer visibleContainer : manager.getVisibleContainers(
				resourceDescription, index)) {
			classDescriptions.addAll(toCollection(visibleContainer
					.getExportedObjectsByType(type)));
		}
		return classDescriptions;
	}

	static <E> Collection<E> toCollection(Iterable<E> iterable) {
		return (iterable instanceof Collection) ? (Collection<E>) iterable
				: Lists.newArrayList(iterable);
	}
}
