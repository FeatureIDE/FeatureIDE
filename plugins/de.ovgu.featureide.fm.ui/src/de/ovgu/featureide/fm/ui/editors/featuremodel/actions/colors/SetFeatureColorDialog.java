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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors;

import static de.ovgu.featureide.fm.core.localization.StringTable.CHOOSE_ACTION_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHOOSE_COLOR_;
import static de.ovgu.featureide.fm.core.localization.StringTable.COLORATION_DIALOG;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATURE_ALL_CHILDREN;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATURE_DIRECT_CHILDREN;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATURE_SIBLINGS;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableItem;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Sets the color of the features in the feature diagram.
 * The color is chosen in the dialog.
 * 
 * @author Christian Elzholz, Marcus Schmelz
 * @author Marcus Pinnecke
 */
public class SetFeatureColorDialog extends Dialog {

	private final static Image colorImage = FMUIPlugin.getDefault().getImageDescriptor("icons/FeatureColorIcon.gif").createImage();
	
	private static final Color WHITE = new Color(null, 255, 255, 255);
	final protected List<IGraphicalFeature> featureList;
	protected ArrayList<IGraphicalFeature> featureListBuffer = new ArrayList<>();
	private FeatureColor newColor = FeatureColor.NO_COLOR;
	private Combo colorDropDownMenu;

	/**
	 * @param parentShell
	 * @param featurelist
	 */
	protected SetFeatureColorDialog(Shell parentShell, List<IGraphicalFeature> featurelist) {
		super(parentShell);
		this.featureList = featurelist;
		setShellStyle(SWT.DIALOG_TRIM | SWT.MIN | SWT.RESIZE);
	}

	/**
	 * @param newshell
	 * 
	 *            Sets the minimal size and the text in the title of the dialog.
	 */
	protected void configureShell(Shell newShell) {
		newShell.setMinimumSize(new Point(500, 500));
		super.configureShell(newShell);
		newShell.setText(COLORATION_DIALOG);
		newShell.setImage(colorImage);
	}

	protected Point getInitialSize() {
		return new Point(500, 500);
	}

	/**
	 * @param parent
	 * 
	 *            Creates the general layout of the dialog.
	 */
	protected Control createDialogArea(Composite parent) {
		final Composite container = (Composite) super.createDialogArea(parent);
		container.setBackground(new Color(parent.getDisplay(), 255, 255, 255));
		GridLayout gridLayout = (GridLayout) container.getLayout();
		gridLayout.numColumns = 2;

		GridData gridData = new GridData();
		gridData.verticalAlignment = GridData.BEGINNING;
		gridData.horizontalAlignment = GridData.FILL;

		Label actionLabel = new Label(container, SWT.NONE);
		actionLabel.setLayoutData(gridData);
		actionLabel.setBackground(WHITE);
		actionLabel.setText(CHOOSE_ACTION_);

		final Combo actionDropDownMenu = new Combo(container, SWT.DROP_DOWN | SWT.READ_ONLY);
		final String[] actionDropDownItems = { SELECTED_FEATURE, SELECTED_FEATURE_DIRECT_CHILDREN, SELECTED_FEATURE_ALL_CHILDREN, SELECTED_FEATURE_SIBLINGS };
		actionDropDownMenu.setLayoutData(gridData);
		actionDropDownMenu.setItems(actionDropDownItems);

		Label chooseColorLabel = new Label(container, SWT.NONE);
		chooseColorLabel.setLayoutData(gridData);
		chooseColorLabel.setBackground(WHITE);
		chooseColorLabel.setText(CHOOSE_COLOR_);

		colorDropDownMenu = new Combo(container, SWT.DROP_DOWN | SWT.READ_ONLY);
		final String[] colorDropDownItems = new String[FeatureColor.values().length];
		int i = 0;
		for (FeatureColor color : FeatureColor.values()) {
			colorDropDownItems[i++] = color.getColorName();
		}
		
		colorDropDownMenu.setLayoutData(gridData);
		colorDropDownMenu.setItems(colorDropDownItems);

		Label featureLabel = new Label(container, SWT.NONE);
		featureLabel.setLayoutData(gridData);
		featureLabel.setBackground(WHITE);
		featureLabel.setText(FEATURES_);

		gridData = new GridData();
		gridData.verticalAlignment = GridData.FILL;
		gridData.horizontalAlignment = GridData.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;

		final Table featureTable = new Table(container, SWT.BORDER | SWT.NO_FOCUS | SWT.HIDE_SELECTION);
		featureTable.setLayoutData(gridData);

		SelectionListener colorSelectionListener = new SelectionListener() {
			public void widgetSelected(SelectionEvent event) {
				String selectedColor = colorDropDownMenu.getItem(((Combo) event.widget).getSelectionIndex());
				FeatureColor color = FeatureColor.getColor(selectedColor);
				for (int j = 0; j < featureListBuffer.size(); j++) {
					if (color != FeatureColor.NO_COLOR) {
						featureTable.getItem(j).setBackground(new Color(null, ColorPalette.getRGB(color.getValue(), 0.4f)));
					} else {
						featureTable.getItem(j).setBackground(WHITE);
					}
				}
				newColor = color;
			}

			public void widgetDefaultSelected(SelectionEvent e) {
			};
		};
		colorDropDownMenu.addSelectionListener(colorSelectionListener);
		colorDropDownMenu.select(0);
		
		
		SelectionListener actionSelectionListener = new SelectionListener() {
			public void widgetSelected(SelectionEvent event) {
				bufferSelectedFeatures();
				String selectedAction = ((Combo) event.widget).getText();
				if (selectedAction.equals(SELECTED_FEATURE_DIRECT_CHILDREN)) {
					findDirectChildren();
				} else if (selectedAction.equals(SELECTED_FEATURE_ALL_CHILDREN)) {
					findAllChildren();
				} else if (selectedAction.equals(SELECTED_FEATURE_SIBLINGS)) {
					findSiblings();
				}
				featureTable.redraw();
				featureTable.removeAll();
				colorPreview(featureTable);
			}

			private void findSiblings() {
				final ArrayList<IGraphicalFeature> affectedFeatures = new ArrayList<>();
				if (!featureListBuffer.isEmpty()) {
					IGraphicalFeatureModel model = featureListBuffer.get(0).getGraphicalModel();
					for (int j = 0; j < featureListBuffer.size(); j++) {
						if (!featureListBuffer.get(j).getObject().getStructure().isRoot()) {
							affectedFeatures.addAll(FeatureUIHelper.getGraphicalChildren(featureListBuffer.get(j).getObject().getStructure().getParent().getFeature(), model));
						}
					}
				}
				featureListBuffer = affectedFeatures;
			}

			private void findAllChildren() {
				final ArrayList<IGraphicalFeature> affectedFeatures = new ArrayList<>();
				for (int j = 0; j < featureListBuffer.size(); j++) {
					affectedFeatures.addAll(findAllChildren(featureListBuffer.get(j)));
				}
				featureListBuffer = affectedFeatures;
			}
			
			private ArrayList<IGraphicalFeature> findAllChildren(IGraphicalFeature item) {
				final ArrayList<IGraphicalFeature> affectedFeatures = new ArrayList<>();
				final List<IGraphicalFeature> children = findChildren(item);
				affectedFeatures.addAll(children);
				for (int j = 0; j < children.size(); j++)
					affectedFeatures.addAll(findAllChildren(children.get(j)));
				return affectedFeatures;
			}
			
			private List<IGraphicalFeature> findChildren(IGraphicalFeature parent) {
				return Functional.toList(FeatureUIHelper.getGraphicalChildren(parent));
			}

			private void findDirectChildren() {
				final ArrayList<IGraphicalFeature> affectedFeatures = new ArrayList<>();
				for (int j = 0; j < featureListBuffer.size(); j++) {
					affectedFeatures.addAll(findChildren(featureListBuffer.get(j)));
				}
				featureListBuffer = affectedFeatures;
			}

		

			public void widgetDefaultSelected(SelectionEvent e) {
			};
		};
		actionDropDownMenu.addSelectionListener(actionSelectionListener);
		
		actionDropDownMenu.select(0);
		bufferSelectedFeatures();
		featureTable.redraw();
		featureTable.removeAll();
		colorPreview(featureTable);
		return parent;

	}

	private void bufferSelectedFeatures() {
		featureListBuffer.clear();
		for (int i = 0; i < featureList.size(); i++) {
			featureListBuffer.add(featureList.get(i));
		}
	}
	
	/**
	 * @param featureTable
	 *            Colors the background of the table items to show a preview of the changed colors
	 */
	private void colorPreview(final Table featureTable) {
		for (int i = 0; i < featureListBuffer.size(); i++) {
			TableItem item = new TableItem(featureTable, SWT.NONE);
			item.setText(featureListBuffer.get(i).getObject().getName());
			FeatureColor color = FeatureColor.getColor(colorDropDownMenu.getText()); 
			if (color != FeatureColor.NO_COLOR) {
				item.setBackground(new Color(null, ColorPalette.getRGB(color.getValue(), 0.4f)));
			} else {
				item.setBackground(WHITE);
			}
		}
	}
	
	/**
	 * @param parent
	 */
	protected Control createContents(Composite parent) {
		super.createContents(parent);
		return parent;
	}

	protected void okPressed() {
		for (int i = 0; i < featureListBuffer.size(); i++) {
			final IFeature feature = featureListBuffer.get(i).getObject();
			FeatureColorManager.setColor(feature, newColor);
		}
		super.okPressed();
	}
}
