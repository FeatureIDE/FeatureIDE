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
package de.ovgu.featureide.fm.core.conf;

import java.nio.file.Paths;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.FeatureGraphFormat;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

public class CreateAndSaveFeatureGraphJob extends CreateFeatureGraphJob {

	private final String path;

	public CreateAndSaveFeatureGraphJob(IFeatureModel featureModel, String path) {
		super(new CreateFeatureGraphJob.Arguments(featureModel));
		this.path = path;
	}

	@Override
	public IFeatureGraph execute(IMonitor workMonitor) throws Exception {
		final FeatureGraphFormat format = new FeatureGraphFormat();
		IFeatureGraph fg = createFeatureGraph(workMonitor);
		FileHandler.save(Paths.get(path), fg, format);
		return fg;
	}

}
