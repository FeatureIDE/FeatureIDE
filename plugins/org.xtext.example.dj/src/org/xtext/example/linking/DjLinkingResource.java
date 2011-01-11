/**
 * 
 */
package org.xtext.example.linking;

import java.io.IOException;
import java.io.OutputStream;
import java.util.Map;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.xtext.linking.lazy.LazyLinkingResource;


public class DjLinkingResource extends LazyLinkingResource {
	/**
	 * The uri of the implicit resource containing the implicit object 
	 */
	public static URI implicitSystemUri = URI.createURI("http:///System.dj");
	
	@Override
	protected void doLinking() {
		ensureSystemIsPresent();
		super.doLinking();
	}

	/**
	 * Ensures that in the resource set there is the implicit Object resource
	 */
	private void ensureSystemIsPresent() {
		// retrieve the implicit Object resource
		ResourceSet resourceSet = getResourceSet();
		Resource res = resourceSet.getResource(implicitSystemUri, true);
		if (res != null) {
			// store the implicit object locally for later use
			return;
		}
	}
	
	/**
	 * Utility method returning the implicit Object in the resource
	 * set of the specified element
	 * 
	 * @param eObject
	 * @return
	 */
	/*public static Interface getIObjectInterface(EObject eObject) {
		return ((RtjLinkingResource)eObject.eResource()).getIObjectInterface();
	}*/
	
	/*public Interface getIObjectInterface() {
		return (Interface)ElementFactory.getFactory().forName("IObject");
	}*/

	@Override
	public void doSave(OutputStream outputStream, Map<?, ?> options)
			throws IOException {
		// don't save the implicit resource
		if (getURI().equals(implicitSystemUri))
			return;
		
		super.doSave(outputStream, options);
	}
}
