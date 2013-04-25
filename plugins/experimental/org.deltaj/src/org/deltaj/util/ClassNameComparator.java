/**
 * 
 */
package org.deltaj.util;

import java.util.Comparator;

import org.deltaj.deltaj.Class;

/**
 * Compares two classes using their names
 * 
 * @author bettini
 *
 */
public class ClassNameComparator implements Comparator<Class> {

	@Override
	public int compare(Class arg0, Class arg1) {
		return arg0.getName().compareTo(arg1.getName());
	}
	
}
