/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.configuration;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public interface IConfiguration {

	public boolean canBeValid();

	public FeatureModel getFeatureModel();

	public List<SelectableFeature> getFeatures();

	public List<SelectableFeature> getManualFeatures();

	public SelectableFeature getRoot();

	public SelectableFeature getSelectablefeature(String name);

	public Set<String> getSelectedFeatureNames();

	public List<Feature> getSelectedFeatures();

	public LinkedList<List<String>> getSolutions(int max) throws TimeoutException;

	public List<Feature> getUnSelectedFeatures();

	public boolean isPropagate();

	public boolean isValid();

	/**
	 * Ignores hidden features.
	 * Use this, when propgate is disabled (hidden features are not updated).
	 */
	public boolean isValidNoHidden();

	public void leadToValidConfiguration(List<SelectableFeature> featureList, WorkMonitor workMonitor);

	public void leadToValidConfiguration(List<SelectableFeature> featureList, int mode, WorkMonitor workMonitor);

	/**
	 * Turns all automatic into manual values
	 * 
	 * @param discardDeselected if {@code true} all automatic deselected features get undefined instead of manual deselected
	 */
	public void makeManual(boolean discardDeselected);

	/**
	 * Convenience method.
	 * 
	 * @return the values of number(250)
	 * @see #number(long)
	 */
	public long number();

	/**
	 * Counts the number of possible solutions.
	 * 
	 * @return a positive value equal to the number of solutions (if the method terminated in time)</br>
	 *         or a negative value (if a timeout occured) that indicates that there are more solutions than the absolute value
	 */
	public long number(long timeout);

	public void resetValues();

	public void setManual(SelectableFeature feature, Selection selection);

	public void setManual(String name, Selection selection);

	public void setPropagate(boolean propagate);

	public String toString();

	public void update();

	public void update(boolean redundantManual, String startFeatureName);

	void setAutomatic(SelectableFeature feature, Selection automatic);

	void setAutomatic(String name, Selection selected);

	public IConfigurationPropagator getPropagator();

}