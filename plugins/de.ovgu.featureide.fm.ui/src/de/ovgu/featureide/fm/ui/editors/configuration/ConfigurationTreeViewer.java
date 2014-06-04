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
package de.ovgu.featureide.fm.ui.editors.configuration;

import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;

/**
 * requires a configuration as input (via setInput) and additionally a feature
 * model with the constructor
 * 
 * @author Christian Kaestner
 */
public class ConfigurationTreeViewer extends TreeViewer {

	public ConfigurationTreeViewer(Composite parent, int style,
			FeatureModel model) {
		super(parent, style);
		setContentProvider(new ConfigurationContentProvider());
		setLabelProvider(new AdvancedConfigurationLabelProvider());
		addDoubleClickListener(new IDoubleClickListener() {

			public void doubleClick(DoubleClickEvent event) {
				Object object = ((ITreeSelection) event.getSelection())
						.getFirstElement();
				if (object instanceof SelectableFeature) {
					final SelectableFeature feature = (SelectableFeature) object;
					if (feature.getAutomatic() == Selection.UNDEFINED) {
						// set to the next value
						if (feature.getManual() == Selection.UNDEFINED)
							set(feature, Selection.SELECTED);
						else if (feature.getManual() == Selection.SELECTED)
							set(feature, Selection.UNSELECTED);
						else
							// case: unselected
							set(feature, Selection.UNDEFINED);
						fireChanged();
						ConfigurationTreeViewer.this.refresh();
					}
				}
			}

			private void set(SelectableFeature feature, Selection selection) {
				assert getInput() instanceof Configuration;
				((Configuration) getInput()).setManual(feature, selection);
			}

		});

	}

	protected void fireChanged() {
		for (PropertyChangeListener l : listeners)
			l.propertyChange(null);
	}

	private final List<PropertyChangeListener> listeners = new ArrayList<PropertyChangeListener>();

	public void addChangeListener(PropertyChangeListener listener) {
		listeners.add(listener);
	}

	public void removeChangeListener(PropertyChangeListener listener) {
		listeners.remove(listener);
	}

}
