package de.ovgu.featureide.fm.attributes.properties;

import java.io.IOException;
import java.io.InputStream;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.core.runtime.content.IContentTypeManager;

import de.ovgu.featureide.fm.attributes.base.impl.EFMFormatManager;
import de.ovgu.featureide.fm.attributes.format.XmlExtendedFeatureModelFormat;
import de.ovgu.featureide.fm.core.ExtensionManager.NoSuchExtensionException;
import de.ovgu.featureide.fm.core.base.impl.FormatManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

public class ExtendedFormatTester extends PropertyTester {

	private FormatManager<?> getFormatManager(String property) {
		switch (property) {
		case "extendedfeaturemodel":
			return EFMFormatManager.getInstance();
		default:
			return null;
		}
	}

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		final IFile res = SelectionWrapper.checkClass(receiver, IFile.class);
		if (res != null) {
			final FormatManager<?> formatManager = getFormatManager(property);
			return checkFormat(formatManager, res);
		}
		return false;
	}

	static boolean checkFormat(FormatManager<?> formatManager, final IFile res) {
		if (formatManager != null) {
			final IContentTypeManager contentTypeManager = Platform.getContentTypeManager();
			final IContentType[] findContentTypesFor;
			try (InputStream contents = res.getContents()) {
				findContentTypesFor = contentTypeManager.findContentTypesFor(contents, res.getName());
			} catch (IOException | CoreException e) {
				FMUIPlugin.getDefault().logError(e);
				return false;
			}
			try (InputStream contents = res.getContents()) {
				final LazyReader lazyReader = new LazyReader(contents);
				for (final IContentType contentType : findContentTypesFor) {
					final Object formatProperty =
						contentType.getDefaultDescription().getProperty(new QualifiedName("de.ovgu.featureide.fm.ui.contentType", "format"));
					if (formatProperty != null) {
						try {
							final IPersistentFormat<?> extension = formatManager.getExtension(formatProperty.toString());
							if (extension instanceof XmlExtendedFeatureModelFormat && extension.supportsContent(lazyReader)) {
								return true;
							}
						} catch (final NoSuchExtensionException e) {}
					}
				}
			} catch (IOException | CoreException e) {
				FMUIPlugin.getDefault().logError(e);
			}
		}
		return false;
	}
}
