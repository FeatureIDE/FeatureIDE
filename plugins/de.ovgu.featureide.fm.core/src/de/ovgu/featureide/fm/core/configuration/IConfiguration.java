/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.LinkedList;
import java.util.List;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * Provides long running operations for the configuration process.
 */
public interface IConfiguration {	
	boolean canBeValid();
	LinkedList<List<String>> getSolutions(int max) throws TimeoutException;
	boolean isValid();
	boolean[] leadToValidConfiguration(List<SelectableFeature> featureList, WorkMonitor workMonitor);
	boolean[] leadToValidConfiguration(List<SelectableFeature> featureList, int mode, WorkMonitor workMonitor);
	long number(long timeout);
	void update(boolean manual, boolean redundantManual);
}
