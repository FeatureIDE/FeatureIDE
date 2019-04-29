package de.ovgu.featureide.fm.ui.properties;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.base.impl.FormatManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

public class FormatFolderTester extends PropertyTester {

	public FormatFolderTester() {}

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		final IContainer res = SelectionWrapper.checkClass(receiver, IContainer.class);
		if (res != null) {
			final List<IFile> files = new ArrayList<>();
			try {
				res.accept(new IResourceVisitor() {
					@Override
					public boolean visit(IResource child) throws CoreException {
						if (child instanceof IFile) {
							files.add((IFile) child);
						}
						return true;
					}
				}, IResource.DEPTH_ONE, IResource.NONE);
				if (!files.isEmpty()) {
					final FormatManager<?> formatManager = getFormatManager(property);
					final FormatTester formatTester = new FormatTester();
					for (final IFile file : files) {
						if (formatTester.checkFormat(formatManager, file, expectedValue)) {
							return true;
						}
					}
				}
			} catch (final CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}

		}
		return false;
	}

	private FormatManager<?> getFormatManager(String property) {
		switch (property) {
		case "featureModelFolder":
			return FMFormatManager.getInstance();
		case "configurationFolder":
			return ConfigFormatManager.getInstance();
		default:
			return null;
		}
	}

}
