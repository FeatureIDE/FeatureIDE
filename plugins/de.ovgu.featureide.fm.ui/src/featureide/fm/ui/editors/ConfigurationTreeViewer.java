/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.fm.ui.editors;

import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;

import featureide.fm.core.FeatureModel;
import featureide.fm.core.configuration.Configuration;
import featureide.fm.core.configuration.SelectableFeature;
import featureide.fm.core.configuration.Selection;
import featureide.fm.ui.editors.configuration.ConfigurationContentProvider;
import featureide.fm.ui.editors.configuration.ConfigurationLabelProvider;

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
		setLabelProvider(new ConfigurationLabelProvider());
		addDoubleClickListener(listener);
	}

	private IDoubleClickListener listener = new IDoubleClickListener() {

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

	};

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
