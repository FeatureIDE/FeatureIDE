/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base.impl;

import de.ovgu.featureide.fm.core.IExtensionLoader;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.IFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.cnf.CNFFormat;
import de.ovgu.featureide.fm.core.io.dimacs.DIMACSFormat;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslFormat;
import de.ovgu.featureide.fm.core.io.splconquerer.ConquererFMWriter;
import de.ovgu.featureide.fm.core.io.sxfm.SXFMFormat;
import de.ovgu.featureide.fm.core.io.velvet.SimpleVelvetFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;

/**
 * Manages all formats for {@link IFeatureModel feature models}.
 *
 * @author Sebastian Krieter
 */
public final class FMFormatManager extends FormatManager<IFeatureModelFormat> {

	private FMFormatManager() {
		super(XmlFeatureModelFormat.class, SimpleVelvetFeatureModelFormat.class, DIMACSFormat.class, SXFMFormat.class, GuidslFormat.class,
				ConquererFMWriter.class, CNFFormat.class);
	}

	private static FMFormatManager instance = new FMFormatManager();

	public static FMFormatManager getInstance() {
		return instance;
	}

	public static void setExtensionLoader(IExtensionLoader<IFeatureModelFormat> extensionLoader) {
		instance.setExtensionLoaderInternal(extensionLoader);
	}

	public static IFeatureModelFormat getDefaultFormat() {
		return new XmlFeatureModelFormat();
	}

}
