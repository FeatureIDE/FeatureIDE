/**
 * 
 */
package org.xtext.example.linking;

import java.util.Collections;
import java.util.List;
import java.util.Map;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.xtext.linking.impl.DefaultLinkingService;
import org.eclipse.xtext.linking.impl.IllegalNodeException;
import org.eclipse.xtext.parsetree.AbstractNode;
import org.eclipse.xtext.parsetree.LeafNode;
import org.xtext.example.dJ.Class;


public class DjLinkingService extends DefaultLinkingService {

	@Override
	public List<EObject> getLinkedObjects(EObject context, EReference ref,
			AbstractNode node) throws IllegalNodeException {

		List<EObject> linkedObjects = super
				.getLinkedObjects(context, ref, node);
		
		if(ref.getName().equals("extendsList")
				|| ref.getName().equals("interfaceType") ||
				ref.getName().equals("implementsList")) {
			final String s = ((LeafNode)node).getText();
			ElementFactory factory = ElementFactory.getFactory();
			Map<String, Class> elements = factory.getElements();
			if(elements.containsKey(s))
				return Collections.<EObject> singletonList(elements.get(s));
		}

		return linkedObjects;
	}
}
