package de.ovgu.featureide.fm.ui.editors;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.content.IContentDescriber;
import org.eclipse.core.runtime.content.IContentDescription;

import de.ovgu.featureide.fm.core.base.impl.FMFormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.LazyReader;

public class XMLFeatureModelContentDescriber implements IContentDescriber {

	@Override
	public int describe(InputStream contents, IContentDescription description) throws IOException {
		final LazyReader lazyReader = new LazyReader(contents);
		for (final IFeatureModelFormat format : FMFormatManager.getInstance().getExtensions()) {
			if (format.supportsContent(lazyReader)) {
				return IContentDescriber.VALID;
			}
		}
		return IContentDescriber.INVALID;
	}

	@Override
	public QualifiedName[] getSupportedOptions() {
		return null;
	}

}
