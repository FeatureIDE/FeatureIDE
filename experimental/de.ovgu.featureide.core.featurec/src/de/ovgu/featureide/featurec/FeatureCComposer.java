/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.featurec;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ConfigFormatManager;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

public class FeatureCComposer extends ComposerExtensionClass {

	private final FeatureHouseComposer composer;
	private static final String MAPPINGS_FILENAME = ".autotools_mappings";
	private static final Map<String, String> config_parameter = new HashMap<String, String>();

	public FeatureCComposer() {
		composer = new FeatureHouseComposer();
	}

	@Override
	public Mechanism getGenerationMechanism() {
		return composer.getGenerationMechanism();
	}

	@Override
	public void performFullBuild(final IFile config) {
		composer.initialize(CorePlugin.getFeatureProject(config));
		composer.performFullBuild(config);

		final IFeatureModel model = CorePlugin.getFeatureProject(config)
				.getFeatureModel();
		final Configuration cfg = new Configuration(model);
		FileHandler.load(Paths.get(config.getLocationURI()), cfg, ConfigFormatManager.getInstance());

		final IResource mappings = config.getProject().findMember(
				MAPPINGS_FILENAME);
		if ((mappings != null) && mappings.isAccessible()
				&& (mappings instanceof IFile)) {
			try {
				final List<String> content_lines = Files.readAllLines(Paths
						.get(mappings.getLocation().toOSString()), Charset
						.availableCharsets().get("UTF-8"));
				for (final String line : content_lines) {
					final String[] key_value = line.split(";");
					if (key_value.length == 2) {
						config_parameter.put(key_value[0], key_value[1]);
					} else {
						CorePlugin.getDefault().logError(
								"Mappings file invalid",
								new IllegalArgumentException());
					}

				}
			} catch (final IOException e) {
				e.printStackTrace();
			}
		}

		final StringBuilder sb = new StringBuilder();
		for (final SelectableFeature sbf : cfg.getFeatures()) {
			if (sbf.getSelection() == Selection.SELECTED) {
				String str = config_parameter.get(sbf.getName());
				if (str == null) {
					str = "";
					config_parameter.put(sbf.getName(), str);
				}
				sb.append(str).append(" ");
			}
		}
		final IResource autotools_default = config.getProject().findMember(
				".autotools_default");
		if (autotools_default.isAccessible()
				&& (autotools_default instanceof IFile)) {
			try {
				String content = new String(Files.readAllBytes(Paths
						.get(autotools_default.getLocation().toOSString())));
				content = content.replace("@@", sb.toString());
				final IFile auto_tools = (IFile) config.getProject()
						.findMember(".autotools");
				if (auto_tools.isAccessible()) {
					try (InputStream inputStream = new ByteArrayInputStream(
							content.getBytes("UTF-8"))) {
						auto_tools.setContents(inputStream, true, true,
								new NullProgressMonitor());
						// auto_tools.refreshLocal(IResource.DEPTH_INFINITE,
						// null);
					} catch (final CoreException e) {
						e.printStackTrace();
					}

					System.out.println(Files.readAllLines(
							Paths.get(auto_tools.getLocation().toOSString()),
							Charset.availableCharsets().get("UTF-8")));
				}

			} catch (final IOException e) {
				e.printStackTrace();
			}
		}

	}

}
