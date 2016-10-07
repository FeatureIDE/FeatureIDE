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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import java.util.List;

import org.w3c.dom.Document;

import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.io.IConfigurationFormat;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.Problem;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.AXMLFormat;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * Extended configuration format for FeatureIDE projects in XML structure.
 * 
 * @author Sebastian Krieter
 */
public class XMLConfFormat extends AXMLFormat<Configuration> implements IConfigurationFormat {

	public static final String ID = PluginID.PLUGIN_ID + ".format.config." + XMLConfFormat.class.getSimpleName();
	public static final String EXTENSION = StringTable.CONF;

	@Override
	public IPersistentFormat<Configuration> getInstance() {
		return null;
	}

	@Override
	public boolean supportsRead() {
		return false;
	}

	@Override
	public boolean supportsWrite() {
		return false;
	}

	@Override
	protected void readDocument(Document doc, List<Problem> warnings) throws UnsupportedModelException {

	}

	@Override
	protected void writeDocument(Document doc) {

	}

	@Override
	public String getId() {
		return ID;
	}

}
