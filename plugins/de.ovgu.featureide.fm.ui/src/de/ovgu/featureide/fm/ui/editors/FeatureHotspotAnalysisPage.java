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
package de.ovgu.featureide.fm.ui.editors;

import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURE_HOTSPOT_ANALYSIS;
import static de.ovgu.featureide.fm.core.localization.StringTable.HOTSPOT_START_ANALYSIS;
import static de.ovgu.featureide.fm.core.localization.StringTable.HOTSPOT_THRESHOLD;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Spinner;

import de.ovgu.featureide.fm.core.IHotSpotAnalyzer;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Display the hotspot analysis for the feature model.
 * 
 * @author Christopher Kruczek
 * @author Andy Kenner
 */
public class FeatureHotspotAnalysisPage extends FeatureModelEditorPage {

	private static final String ID = FMUIPlugin.PLUGIN_ID + ".editors.FeatureHotSpotAnalysis";
	private static final String PAGE_TEXT = FEATURE_HOTSPOT_ANALYSIS;
	private Spinner thresholdSpinner;
	private Button startAnalysisButton;
	private IFeatureModel model;
	private IHotSpotAnalyzer analyzer;
	
	public FeatureHotspotAnalysisPage(FeatureModelEditor featureModelEditor) {
		model = featureModelEditor.getFeatureModel().clone();
		model.removeConstraint(0);
		this.featureModelEditor = new FeatureModelEditor();
		this.featureModelEditor.featureModel = model;
	}

	@Override
	public String getID() {
		return ID;
	}

	@Override
	public String getPageText() {
		return PAGE_TEXT;
	}

	@Override
	public void createPartControl(Composite parent) {
		super.createPartControl(parent);

		// parent composite
		GridLayout gridLayout = new GridLayout(1, false);
		gridLayout.verticalSpacing = 4;
		gridLayout.marginHeight = 2;
		gridLayout.marginWidth = 0;
		parent.setLayout(gridLayout);

		// 1. sub composite
		GridData gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = false;
		gridData.verticalAlignment = SWT.TOP;
		
		gridLayout = new GridLayout(4, false);
		gridLayout.marginHeight = 0;
		gridLayout.marginWidth = 0;
		gridLayout.marginLeft = 4;
		final Composite compositeTop = new Composite(parent, SWT.NONE);
		compositeTop.setLayout(gridLayout);
		compositeTop.setLayoutData(gridData);

		// info label
		gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = false;
		gridData.verticalAlignment = SWT.CENTER;
		Label infoLabel = new Label(compositeTop, SWT.NONE);
		infoLabel.setText(HOTSPOT_THRESHOLD);
		infoLabel.setLayoutData(gridData);
		
		// spinner
		gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = false;
		gridData.verticalAlignment = SWT.CENTER;
		thresholdSpinner = new Spinner(compositeTop, SWT.HORIZONTAL);
		thresholdSpinner.setMaximum(80);
		thresholdSpinner.setIncrement(1);
		thresholdSpinner.setLayoutData(gridData);
		
		// analysis button
		gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = false;
		gridData.verticalAlignment = SWT.CENTER;
		startAnalysisButton = new Button(compositeTop, SWT.PUSH);
		startAnalysisButton.setText(HOTSPOT_START_ANALYSIS);
		startAnalysisButton.setLayoutData(gridData);
		
		gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.verticalAlignment = SWT.CENTER;
		Label spacerLabel = new Label(compositeTop, SWT.NONE);
		spacerLabel.setText("");
		spacerLabel.setLayoutData(gridData);
		
		
		// 2. sub composite
		gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.verticalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;
		final Composite compositeBottom = new Composite(parent, SWT.BORDER);
		
		compositeBottom.setLayout(new FillLayout());
		compositeBottom.setLayoutData(gridData);
		
		final FeatureDiagramEditor editor = new FeatureDiagramEditor(featureModelEditor, compositeBottom);
		editor.getControl().getDisplay().asyncExec(new Runnable() {
			public void run() {
				editor.setContents(editor.getGraphicalFeatureModel());
				//pageChange(getDiagramEditorIndex());
				editor.refresh();
			}
		});
	}

}
