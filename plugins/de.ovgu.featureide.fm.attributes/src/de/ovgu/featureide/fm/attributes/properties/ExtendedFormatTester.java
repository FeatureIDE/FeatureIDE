package de.ovgu.featureide.fm.attributes.properties;

import java.nio.file.Paths;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.base.impl.FormatManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.ui.properties.FormatTester;

public class ExtendedFormatTester extends FormatTester {

	protected boolean checkFormat(FormatManager<?> formatManager, final IFile res) {
		if (formatManager != null) {
			final IPersistentFormat<?> formatByContent = formatManager.getFormatByContent(Paths.get(res.getLocationURI()));
			if (formatByContent != null) {
				final String factoryId = FMFactoryManager.factoryWorkspaceProvider.getFactoryWorkspace().getID(formatByContent);
				return ExtendedFeatureModelFactory.ID.equals(factoryId);
			}
		}
		return false;
	}
}
