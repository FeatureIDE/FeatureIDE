package de.ovgu.featureide.fm.ui.properties;

import org.eclipse.core.expressions.PropertyTester;

import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

public class ClassTester extends PropertyTester {

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		try {
			return SelectionWrapper.checkClass(receiver, Class.forName((String) expectedValue)) != null;
		} catch (ClassNotFoundException e) {
		}
		return false;
	}

}
