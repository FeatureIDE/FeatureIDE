package de.ovgu.featureide.ui.variantimport.migration;

import de.ovgu.featureide.core.builder.IComposerExtensionBase;

public class MigrationConfigurationData
{
	public String projectName;
	public IComposerExtensionBase composer;
	public String sourcePath;
	public String configPath;
	public String buildPath;

	public MigrationConfigurationData(String projectName, IComposerExtensionBase composer,
			String sourcePath, String configPath, String buildPath)
	{
		this.projectName = projectName;
		this.composer = composer;
		this.sourcePath = sourcePath;
		this.configPath = configPath;
		this.buildPath = buildPath;
	}
}