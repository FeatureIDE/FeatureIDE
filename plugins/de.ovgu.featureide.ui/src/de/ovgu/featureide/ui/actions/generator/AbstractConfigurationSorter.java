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
package de.ovgu.featureide.ui.actions.generator;

import java.util.Collection;
import java.util.LinkedList;

import org.eclipse.core.runtime.IProgressMonitor;

import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Sorts configurations.<br>
 * Default implementation, does nothing.
 * 
 * @author Jens Meinicke
 */
public class AbstractConfigurationSorter {
	
	/**
	 * This list contains all found configurations to built.<br>
	 * Use <code>getConfiguration()</code> and <code>setConfiguration(c)</code> for synchronizing.
	 */
	protected LinkedList<BuilderConfiguration> configurations = new LinkedList<BuilderConfiguration>(); 

	protected final Collection<String> concreteFeatures;

	public AbstractConfigurationSorter(final FeatureModel featureModel) {
		concreteFeatures = featureModel.getConcreteFeatureNames();// TODO move to implementations
	}
	
	public int sort(final IProgressMonitor monitor) {
		return configurations.size();
	}

	public synchronized void addConfiguration(BuilderConfiguration configuration, boolean sort) {
		configurations.add(configuration);
	}

	public synchronized BuilderConfiguration getConfiguration(boolean sort) {
		if (configurations.isEmpty()) {
			return null;
		}
		BuilderConfiguration c = configurations.getFirst();
		configurations.remove();
		return c;
	}
	
	public int getBufferSize() {
		return configurations.size();
	}
}
