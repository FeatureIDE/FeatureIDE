package de.ovgu.featureide.examples.transformation;
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
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.init.FMCoreLibrary;
import de.ovgu.featureide.fm.core.init.LibraryManager;
import de.ovgu.featureide.fm.core.io.IPersistentFormat;
import de.ovgu.featureide.fm.core.io.dimacs.DIMACSFormat;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.uvl.UVLFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.sxfm.SXFMFormat;
import de.ovgu.featureide.fm.core.io.velvet.SimpleVelvetFeatureModelFormat;

/**
 * A simple configurator without GUI using the FeatureIDE library.
 *
 * @author Thomas Thuem
 * @author Sebastian Krieter
 */
public class FeatureModelTransformation {

	static {
		LibraryManager.registerLibrary(FMCoreLibrary.getInstance());
	}

	
	public static void main(String[] args) {
		final Path path = Paths.get("model.xml");
		IFeatureModel model = FeatureModelManager.load(path);
		List<IPersistentFormat<IFeatureModel>> formats = new ArrayList<>();
		formats.add(new UVLFeatureModelFormat());
		formats.add(new DIMACSFormat());
		formats.add(new SXFMFormat());
		formats.add(new SimpleVelvetFeatureModelFormat());
		for (IPersistentFormat<IFeatureModel> format : formats) {
			saveFeatureModel(model, "model_" + format.getName() + "." + format.getSuffix(), format);
		}
	}
	
	public static void saveFeatureModel(IFeatureModel model, String savePath, IPersistentFormat<IFeatureModel> format) {
		FeatureModelManager.save(model, Paths.get(savePath), format);
	}

}
