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
package de.ovgu.featureide.fm.ui.editors.configuration;

import java.util.Set;
import java.util.stream.Collectors;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramViewer;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.properties.FMPropertyManager;

/**
 * TODO Displays pruned feature diagram based on the features selected in the configuration.
 *
 * @author Andreas Gerasimow
 */
public class TreePreviewPage extends EditorPart implements IConfigurationEditorPage {

	private static final String ID = FMUIPlugin.PLUGIN_ID + "TreePreviewPage";

	private int index;
	private IConfigurationEditor configurationEditor;
	private Composite parent;

	@Override
	public void setIndex(int index) {
		this.index = index;
	}

	@Override
	public int getIndex() {
		return index;
	}

	@Override
	public void setConfigurationEditor(IConfigurationEditor configurationEditor) {
		this.configurationEditor = configurationEditor;
	}

	@Override
	public void propertyChange(FeatureIDEEvent evt) {
		// TODO: Listen for configuration changes
		if (evt != null) {
			if (evt.getSource() instanceof IFeatureModel) {
				switch (evt.getEventType()) {
				case MODEL_DATA_SAVED:
				case MODEL_DATA_OVERWRITTEN:
					refreshPage();
					break;
				default:
					break;
				}
			} else if (evt.getSource() instanceof Configuration) {
				switch (evt.getEventType()) {
				case MODEL_DATA_SAVED:

					break;
				case MODEL_DATA_OVERWRITTEN:
					refreshPage();
					break;
				default:
					break;
				}
			} else {
				if (evt.getEventType() == EventType.CONFIGURABLE_ATTRIBUTE_CHANGED) {
					refreshPage();
				}
			}
		}
	}

	private void refreshPage() {
		for (final Control child : parent.getChildren()) {
			child.dispose();
		}
		final Set<String> selectedFeatures =
			configurationEditor.getConfigurationManager().getVarObject().getSelectedFeatures().stream().map(IFeature::getName).collect(Collectors.toSet());

		final IGraphicalFeatureModel graphicalFeatureModel = new GraphicalFeatureModel(configurationEditor.getFeatureModelManager());
		graphicalFeatureModel.init();

		graphicalFeatureModel.getAllFeatures().forEach((feature) -> {
			if (selectedFeatures.contains(feature.getObject().getName())) {
				feature.setConstraintSelected(true);
				feature.setCollapsed(false);
			} else {
				feature.setCollapsed(true);
			}
		});

		final FeatureDiagramViewer viewer = new FeatureDiagramViewer(graphicalFeatureModel);
		final GridData gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.verticalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		final Composite compositeBottom = new Composite(parent, SWT.FILL);
		compositeBottom.setLayout(new FillLayout());
		compositeBottom.setLayoutData(gridData);
		viewer.createControl(compositeBottom);
		viewer.setContents(graphicalFeatureModel);
		viewer.getControl().addControlListener(viewer.createControlListener());
		viewer.getControl().setBackground(FMPropertyManager.getDiagramBackgroundColor());
		parent.requestLayout();
	}

	@Override
	public void pageChangeFrom(int index) {

	}

	@Override
	public void pageChangeTo(int index) {
		refreshPage();
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		firePropertyChange(IEditorPart.PROP_DIRTY);
	}

	@Override
	public void doSaveAs() {

	}

	@Override
	public void init(IEditorSite site, IEditorInput input) throws PartInitException {
		setSite(site);
		setInput(input);
	}

	@Override
	public boolean isDirty() {
		return false;
	}

	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}

	@Override
	public void createPartControl(Composite parent) {
		this.parent = parent;
	}

	@Override
	public void setFocus() {}

	@Override
	public IConfigurationEditorPage getPage() {
		return this;
	}

	@Override
	public String getID() {
		return ID;
	}

	@Override
	public String getPageText() {
		return StringTable.CONFIGURATION_TREE;
	}

	@Override
	public boolean allowPageChange(int newPageIndex) {
		return true;
	}
}
