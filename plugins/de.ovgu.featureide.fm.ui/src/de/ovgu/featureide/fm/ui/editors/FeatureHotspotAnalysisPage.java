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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Spinner;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;

import de.ovgu.featureide.fm.core.HotSpotResult;
import de.ovgu.featureide.fm.core.IHotSpotAnalyzer;
import de.ovgu.featureide.fm.core.IHotSpotResultInterpreter;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
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
		
		this.featureModelEditor = new FeatureModelEditor();
		this.featureModelEditor.featureModel = model;
		
		analyzer = new IHotSpotAnalyzer() {			
			@Override
			public Set<HotSpotResult> analyze(IFeatureModel fm) {
				Set<HotSpotResult> results = new HashSet<HotSpotResult>(); 
				for(IFeature feature : fm.getFeatures()){
					HotSpotResult rs = new HotSpotResult();
					rs.setFeatureName(feature.getName());
					for(IConstraint constr : fm.getConstraints()){
						if(constr.getContainedFeatures().contains(feature))
							rs.setMetricValue(rs.getMetricValue() + 1);
					}
					results.add(rs);
				}
				return results;
			}
		};
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
		thresholdSpinner.setMaximum(model.getConstraintCount());
		thresholdSpinner.setIncrement(1);
		thresholdSpinner.setSelection(5);
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
		gridData.grabExcessHorizontalSpace = gridData.grabExcessVerticalSpace = true;
		final ScrolledComposite compositeBottom = new ScrolledComposite(parent, SWT.BORDER);
		final Table tbl = createTableBaseLayout(compositeBottom);
		tbl.setVisible(false);
		
		compositeBottom.setContent(tbl);
		compositeBottom.setExpandHorizontal(true);
		compositeBottom.setExpandVertical(true);
		compositeBottom.setAlwaysShowScrollBars(true);
		
		startAnalysisButton.addSelectionListener(new SelectionListener() {
			
			@Override
			public void widgetSelected(SelectionEvent e) {
				Set<HotSpotResult> result = analyzer.analyze(FeatureHotspotAnalysisPage.this.model);
				List<HotSpotResult> sortedResult = new ArrayList<HotSpotResult>(result);
				Collections.sort(sortedResult);
				
				IHotSpotResultInterpreter<Color> interpreter = new ColorMetricHotSpotInterpreter(Integer.valueOf(thresholdSpinner.getText()).intValue());
				
				tbl.setVisible(false);
				tbl.removeAll();
				
				for(HotSpotResult hsr : sortedResult){
					Color c = interpreter.interpret(hsr);
					TableItem item = new TableItem (tbl, SWT.NONE);
					item.setText (0, hsr.getFeatureName());
					item.setText (1, Double.toString(hsr.getMetricValue()));
					item.setText (2, c.toString());
					item.setBackground(c);
					FeatureColorManager.setColor(model.getFeature(hsr.getFeatureName()), c);
				}
				for (int i=0; i < tbl.getColumnCount(); i++) {
					tbl.getColumn(i).pack();
				}
				tbl.setVisible(true);
				tbl.pack();
			}
			
			@Override
			public void widgetDefaultSelected(SelectionEvent e) {
				
			}
		});
		
		compositeBottom.setLayoutData(gridData);
//		gridData = new GridData();
//		gridData.horizontalAlignment = SWT.FILL;
//		gridData.verticalAlignment = SWT.FILL;
//		//gridData.grabExcessHorizontalSpace = true;
//		gridData.grabExcessVerticalSpace = true;
		
		//final Composite compositeBottomFMInner = new Composite(compositeBottom, SWT.BORDER);
		//compositeBottomFMInner.setLayoutData(gridData);
		
//		final FeatureDiagramEditor editor = new FeatureDiagramEditor(featureModelEditor, compositeBottomFMInner);
//		editor.getControl().getDisplay().asyncExec(new Runnable() {
//			public void run() {
//				editor.setContents(editor.getGraphicalFeatureModel());
//				//pageChange(getDiagramEditorIndex());
//				editor.refresh();
//			}
//		});
	}

	private Table createTableBaseLayout(Composite parent){
		Table tbl = new Table(parent,SWT.BORDER | SWT.V_SCROLL);
		String titles[] = {"Feature Name","Metric Result","RGB Value"};
		tbl.setLinesVisible (true);
		tbl.setHeaderVisible (true);
		GridData gd = new GridData(SWT.FILL,SWT.TOP,true,false);
		for(int i =0; i < titles.length; i++){
			TableColumn col = new TableColumn(tbl, SWT.NONE);
			col.setWidth(150);
			col.setText(titles[i]);
		}
		tbl.setLayoutData(gd);
		return tbl;
	}
	
	private void createAnalysisResultView(Composite compositeBottom) {
		
	}

}
