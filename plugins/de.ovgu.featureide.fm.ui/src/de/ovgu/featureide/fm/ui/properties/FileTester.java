package de.ovgu.featureide.fm.ui.properties;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

public class FileTester extends PropertyTester {

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		final IFile res = (IFile) SelectionWrapper.checkClass(receiver, IFile.class);
		if (res != null) {
			for (int i = 0; i < args.length; i++) {
				if (res.getName().endsWith((String) args[i])) {
					return true;
				}
			}
		}
		return false;
	}

}
