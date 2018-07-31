package de.ovgu.featureide.fm.attributes.base.impl;

import de.ovgu.featureide.fm.attributes.format.XmlExtendedFeatureModelFormat;
import de.ovgu.featureide.fm.core.IExtensionLoader;
import de.ovgu.featureide.fm.core.base.impl.FormatManager;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;

public class EFMFormatManager extends FormatManager<IFeatureModelFormat> {

	private EFMFormatManager() {
		super(XmlExtendedFeatureModelFormat.class);
	}

	private static EFMFormatManager instance = new EFMFormatManager();

	public static EFMFormatManager getInstance() {
		return instance;
	}

	public static void setExtensionLoader(IExtensionLoader<IFeatureModelFormat> extensionLoader) {
		instance.setExtensionLoaderInternal(extensionLoader);
	}

	public static IFeatureModelFormat getDefaultFormat() {
		return new XmlExtendedFeatureModelFormat();
	}
}
