package de.ovgu.featureide.fm.attributes.format;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.io.LazyReader;
import de.ovgu.featureide.fm.core.io.uvl.UVLFeatureModelFormat;

public class UVLExtendedFeatureModelFormat extends UVLFeatureModelFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format." + UVLExtendedFeatureModelFormat.class.getSimpleName();

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public boolean supportsContent(CharSequence content) {
		return content.toString().contains(EXTENDED_ATTRIBUTE_NAME);
	}

	@Override
	public boolean supportsContent(LazyReader reader) {
		return supportsContent((CharSequence) reader);
	}
}
