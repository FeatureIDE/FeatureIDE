/**
 * 
 */
package org.xtext.example.linking;

import java.util.Collection;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceFactory;
import org.xtext.example.dJ.Class;
import org.xtext.example.dJ.Core;
import org.xtext.example.dJ.Module;
import org.xtext.example.dJ.Program;
import org.xtext.example.dJ.DJFactory;

import com.google.inject.Inject;
import com.google.inject.Provider;

public class DjResourceFactory extends XtextResourceFactory {
	private static Resource systemResource;

	@Inject
	public DjResourceFactory(Provider<XtextResource> resourceProvider) {
		super(resourceProvider);
	}

	/**
	 * If asked for the implicit Object URI, it synthesizes such a resource
	 * 
	 * @see
	 * org.eclipse.xtext.resource.XtextResourceFactory#createResource(org.eclipse
	 * .emf.common.util.URI)
	 */
	@Override
	public Resource createResource(URI uri) {
		if (uri.equals(DjLinkingResource.implicitSystemUri)) {
			DjLinkingResource resource = new DjLinkingResource();
			resource.getContents().add(createSystemFile());
			resource.setURI(uri);
			systemResource = resource;
			return resource;
		}

		return super.createResource(uri);
	}
	
	/**
	 * Returns the system resource.
	 * @return the system resource.
	 */
	public static Resource getSystemResource() {
		return systemResource;
	}

	/**
	 * Creates a program consisting of the single implicit interface IObject
	 * @return program consisting of the single implicit class Object
	 */
	Program createSystemFile() {
		Program file = DJFactory.eINSTANCE.createProgram();
		ElementFactory factory = ElementFactory.getFactory();
		Collection<Class> elementList = factory.getElementList();
		Core core = DJFactory.eINSTANCE.createCore();
		Module module = DJFactory.eINSTANCE.createModule();
	
		module.setCore(core);
		file.getModulesList().add(module);

		for(Class element : elementList) {
			core.getClassesList().add(element);
		}
		
		return file;
	}
}
