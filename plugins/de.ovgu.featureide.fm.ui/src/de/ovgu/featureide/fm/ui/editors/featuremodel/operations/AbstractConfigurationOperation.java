package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import javax.annotation.Nonnull;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;

public abstract class AbstractConfigurationOperation {

	protected static final String ID_PREFIX = PluginID.PLUGIN_ID + ".operation.";

	protected final ConfigurationManager configurationManager;
	protected final String title;

	public AbstractConfigurationOperation(ConfigurationManager configurationManager, String title) {
		this.configurationManager = configurationManager;
		this.title = title;
	}

	protected abstract FeatureIDEEvent operation(Configuration config);

	protected abstract FeatureIDEEvent inverseOperation(Configuration config);

	protected FeatureIDEEvent firstOperation(Configuration config) {
		return operation(config);
	}

	public final void execute() {
		final FeatureIDEEvent event = configurationManager.processObject(this::firstOperation, getChangeIndicator());
		fireEvent(event);
	}

	public final void redo() {
		final FeatureIDEEvent event = configurationManager.processObject(this::operation, getChangeIndicator());
		fireEvent(event);
	}

	public final void undo() {
		final FeatureIDEEvent event = configurationManager.processObject(this::inverseOperation, getChangeIndicator());
		fireEvent(event);
	}

	protected int getChangeIndicator() {
		return ConfigurationManager.CHANGE_ALL;
	}

	protected final void fireEvent(@Nonnull FeatureIDEEvent event) {
		if (event == null) {
			Logger.logWarning(getClass() + " operation() must return a FeatureIDEEvent");
			event = new FeatureIDEEvent(configurationManager, null, null, null);
		}
		configurationManager.fireEvent(event);
	}

	ConfigurationManager getConfigurationManager() {
		return configurationManager;
	}

	public String getTitle() {
		return title;
	}

}
