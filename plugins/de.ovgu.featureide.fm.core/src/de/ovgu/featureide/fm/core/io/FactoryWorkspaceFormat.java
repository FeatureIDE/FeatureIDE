/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.io;

import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.text.ParseException;
import java.util.Map.Entry;
import java.util.Properties;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.impl.FactoryWorkspace;

/**
 * Reads / Writes the content of a {@link FactoryWorkspace}.
 *
 * @author Sebastian Krieter
 */
public class FactoryWorkspaceFormat extends APersistentFormat<FactoryWorkspace> {

	public static final String ID = PluginID.PLUGIN_ID + ".format.fm." + FactoryWorkspaceFormat.class.getSimpleName();

	private static final String DEFAULT_KEY = "default";
	private static final String PREFIX = "$";

	@Override
	public ProblemList read(FactoryWorkspace workspace, CharSequence source) {
		final ProblemList list = new ProblemList();
		final Properties properties = new Properties();
		try (StringReader reader = new StringReader(source.toString())) {
			properties.load(reader);
		} catch (final IOException e) {
			list.add(new Problem(e));
		}

		for (final Entry<Object, Object> entry : properties.entrySet()) {
			final Object key = entry.getKey();
			if (DEFAULT_KEY.equals(key)) {
				workspace.setDefaultFactoryID(entry.getValue().toString());
			} else {
				workspace.assignID(key.toString().substring(PREFIX.length()), entry.getValue().toString());
			}
		}

		if (workspace.getDefaultFactoryID() == null) {
			list.add(new Problem(new ParseException("No default Factory specified.", 0)));
		}

		return list;
	}

	@Override
	public String write(FactoryWorkspace workspace) {
		final Properties properties = new Properties();
		properties.setProperty(DEFAULT_KEY, workspace.getDefaultFactoryID());
		for (final Entry<String, String> entry : workspace.getMap().entrySet()) {
			properties.setProperty(PREFIX + entry.getKey(), entry.getValue());
		}
		try (StringWriter writer = new StringWriter()) {
			properties.store(writer, null);
			return writer.toString();
		} catch (final IOException e) {
			Logger.logError(e);
			return null;
		}
	}

	@Override
	public String getSuffix() {
		return "properties";
	}

	@Override
	public boolean supportsRead() {
		return true;
	}

	@Override
	public boolean supportsWrite() {
		return true;
	}

	@Override
	public String getId() {
		return ID;
	}

	@Override
	public String getName() {
		return "";
	}

}
