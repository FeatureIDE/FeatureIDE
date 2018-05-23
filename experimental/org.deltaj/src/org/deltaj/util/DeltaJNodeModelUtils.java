/**
 * 
 */
package org.deltaj.util;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.xtext.nodemodel.util.NodeModelUtils;

/**
 * @author bettini
 * 
 */
public class DeltaJNodeModelUtils {

	public String getProgramText(EObject object) {
		return NodeModelUtils.getTokenText(NodeModelUtils.getNode(object));
	}
}
