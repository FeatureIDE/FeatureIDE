package featureide.core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.Platform;

public abstract class ExtensionPointManager<T extends featureide.core.IExtension> {

	protected final String pluginID;
	protected final String extensionPointID;

	protected ExtensionPointManager(String pluginID, String extensionPointID) {
		this.pluginID = pluginID;
		this.extensionPointID = extensionPointID;
	}

	private List<T> cachedProviders = null;

	private void loadProviders() {
		if (cachedProviders != null)
			return;
		cachedProviders = new ArrayList<T>();
		IExtension[] extensions = Platform.getExtensionRegistry()
				.getExtensionPoint(pluginID, extensionPointID)
				.getExtensions();
		for (IExtension extension : extensions) {
			IConfigurationElement[] configurationElements = extension
					.getConfigurationElements();
			for (IConfigurationElement configurationElement : configurationElements) {
				T proxy = parseExtension(configurationElement);
				if (proxy != null)
					cachedProviders.add(proxy);
			}
		}
		//debugPrintExtensions();
	}

//	private void debugPrintExtensions() {
//		for (T le : getProviders())
//			System.out.println(le);
//	}

	protected abstract T parseExtension(
			IConfigurationElement configurationElement);

	protected List<T> getProviders() {
		loadProviders();
		return Collections.unmodifiableList(cachedProviders);
	}
}
