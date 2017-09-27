/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
<<<<<<< HEAD
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
=======
 * FeatureIDE is free software: you can redistributeinitialSelectedColor/or modify
 * it under the terms of the GNU LinitialSelectedColoreneral PuinitialSelectedColorcense as published by
 * the FreinitialSelectedColorare Foundation, either version 3 of the License, or
>>>>>>> bs_team3_configMap
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

import static de.ovgu.featureide.fm.core.localization.StringTable.CHOOSE_ACTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHOOSE_COLOR;
import static de.ovgu.featureide.fm.core.localization.StringTable.COLORATION_DIALOG;
import static de.ovgu.featureide.fm.core.localization.StringTable.FEATURES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATURE_ALL_CHILDREN;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATURE_DIRECT_CHILDREN;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_FEATURE_SIBLINGS;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.commands.ExecutionException;
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
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.color.ColorPalette;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.SetFeatureColorOperation;

/**
 * Sets the color of the features in the feature diagram. The color is chosen in the dialog.
 *
 * @author Christian Elzholz
 * @author Marcus Schmelz
 * @author Marcus Pinnecke
 * @author Paul Maximilian Bittner
 * @author Niklas Lehnfeld
 * @author Antje Moench
 */
public class SetFeatureColorDialog extends Dialog {

	private final static Image colorImage = FMUIPlugin.getDefault().getImageDescriptor("icons/FeatureColorIcon.gif").createImage();

	private static final Color WHITE = new Color(null, 255, 255, 255);
	private final FeatureColor initialSelectedColor;
	private FeatureColor newColor = FeatureColor.NO_COLOR;

	private final List<IFeature> featureList;
	private ArrayList<IFeature> featureListBuffer = new ArrayList<>();

	private Table featureTable;
	private Combo colorDropDownMenu;

	private boolean enableUndoRedo = false;

	/**
	 * @param parentShell
	 * @param featurelist
	 */
	protected SetFeatureColorDialog(Shell parentShell, List<IFeature> featurelist) {
		this(parentShell, featurelist, null);
	}

	protected SetFeatureColorDialog(Shell parentShell, List<IFeature> featurelist, FeatureColor selectedColor) {
		super(parentShell);
		featureList = featurelist;
		initialSelectedColor = selectedColor;
		setShellStyle(SWT.DIALOG_TRIM | SWT.MIN | SWT.RESIZE);
	}

	protected SetFeatureColorDialog(Shell parentShell, List<IFeature> featurelist, FeatureColor selectedColor, boolean enableUndoRedo) {
		this(parentShell, featurelist, selectedColor);
		this.enableUndoRedo = enableUndoRedo;
	}

	/**
	 * Sets the minimal size and the text in the title of the dialog.
	 *
	 * @param newshell
	 */
	@Override
	protected void configureShell(Shell newShell) {
		newShell.setMinimumSize(new Point(500, 500));
		super.configureShell(newShell);
		newShell.setText(COLORATION_DIALOG);
		newShell.setImage(colorImage);
	}

	@Override
	protected Point getInitialSize() {
		return new Point(500, 500);
	}

	/**
	 * Creates the general layout of the dialog.
	 *
	 * @param parent
	 */
	@Override
	protected Control createDialogArea(Composite parent) {
		final Composite container = (Composite) super.createDialogArea(parent);
		container.setBackground(new Color(parent.getDisplay(), 255, 255, 255));
		final GridLayout gridLayout = (GridLayout) container.getLayout();
		gridLayout.numColumns = 2;

		GridData gridData = new GridData();
		gridData.verticalAlignment = GridData.BEGINNING;
		gridData.horizontalAlignment = GridData.FILL;

		final Label actionLabel = new Label(container, SWT.NONE);
		actionLabel.setLayoutData(gridData);
		actionLabel.setBackground(WHITE);
		actionLabel.setText(CHOOSE_ACTION);

		final Combo actionDropDownMenu = new Combo(container, SWT.DROP_DOWN | SWT.READ_ONLY);
		final String[] actionDropDownItems = { SELECTED_FEATURE, SELECTED_FEATURE_DIRECT_CHILDREN, SELECTED_FEATURE_ALL_CHILDREN, SELECTED_FEATURE_SIBLINGS };
		actionDropDownMenu.setLayoutData(gridData);
		actionDropDownMenu.setItems(actionDropDownItems);

		final Label chooseColorLabel = new Label(container, SWT.NONE);
		chooseColorLabel.setLayoutData(gridData);
		chooseColorLabel.setBackground(WHITE);
		chooseColorLabel.setText(CHOOSE_COLOR);

		colorDropDownMenu = new Combo(container, SWT.DROP_DOWN | SWT.READ_ONLY);
		final String[] colorDropDownItems = new String[FeatureColor.values().length];
		int i = 0;
		int initiallySelectedColorIndex = 0; // NO COLOR
		for (final FeatureColor color : FeatureColor.values()) {
			colorDropDownItems[i] = color.getColorName();
			if ((initialSelectedColor != null) && initialSelectedColor.equals(color)) {
				initiallySelectedColorIndex = i;
			}
			i++;
		}

		colorDropDownMenu.setLayoutData(gridData);
		colorDropDownMenu.setItems(colorDropDownItems);

		final Label featureLabel = new Label(container, SWT.NONE);
		featureLabel.setLayoutData(gridData);
		featureLabel.setBackground(WHITE);
		featureLabel.setText(FEATURES_);

		gridData = new GridData();
		gridData.verticalAlignment = GridData.FILL;
		gridData.horizontalAlignment = GridData.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = true;

		featureTable = new Table(container, SWT.BORDER | SWT.NO_FOCUS | SWT.HIDE_SELECTION);
		featureTable.setLayoutData(gridData);

		final SelectionListener colorSelectionListener = new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent event) {
				onColorSelectionChanged(((Combo) event.widget).getSelectionIndex());
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {};
		};
		colorDropDownMenu.addSelectionListener(colorSelectionListener);

		final SelectionListener actionSelectionListener = new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent event) {
				bufferSelectedFeatures();
				final String selectedAction = ((Combo) event.widget).getText();
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
				final ArrayList<IFeature> affectedFeatures = new ArrayList<>();
				for (final IFeature feature : featureListBuffer) {
					if (!feature.getStructure().isRoot()) {
						for (final IFeatureStructure featureStructure : feature.getStructure().getParent().getChildren()) {
							affectedFeatures.add(featureStructure.getFeature());
						}
					}
				}
				featureListBuffer = affectedFeatures;
			}

			private void findAllChildren() {
				final ArrayList<IFeature> affectedFeatures = new ArrayList<>();
				for (int j = 0; j < featureListBuffer.size(); j++) {
					affectedFeatures.addAll(findAllChildren(featureListBuffer.get(j)));
				}
				featureListBuffer = affectedFeatures;
			}

			private ArrayList<IFeature> findAllChildren(IFeature item) {
				final ArrayList<IFeature> affectedFeatures = new ArrayList<>();
				final List<IFeature> children = findChildren(item);
				affectedFeatures.addAll(children);
				for (int j = 0; j < children.size(); j++) {
					affectedFeatures.addAll(findAllChildren(children.get(j)));
				}
				return affectedFeatures;
			}

			private List<IFeature> findChildren(IFeature parent) {
				final List<IFeature> children = new ArrayList<>();
				for (final IFeatureStructure childStructure : parent.getStructure().getChildren()) {
					children.add(childStructure.getFeature());
				}
				return children;
			}

			private void findDirectChildren() {
				final ArrayList<IFeature> affectedFeatures = new ArrayList<>();
				for (int j = 0; j < featureListBuffer.size(); j++) {
					affectedFeatures.addAll(findChildren(featureListBuffer.get(j)));
				}
				featureListBuffer = affectedFeatures;
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {};
		};
		actionDropDownMenu.addSelectionListener(actionSelectionListener);

		actionDropDownMenu.select(0);
		bufferSelectedFeatures();
		featureTable.redraw();
		featureTable.removeAll();
		colorPreview(featureTable);
		colorDropDownMenu.select(initiallySelectedColorIndex);
		// selection changed is only triggered when user changes the selection, so we have to do it manually
		onColorSelectionChanged(initiallySelectedColorIndex);
		return parent;

	}

	/**
	 * Invoked if the selection in the color combo box has changed.
	 *
	 * @param index The index of the newly selected color.
	 */
	private void onColorSelectionChanged(int index) {
		final String selectedColor = colorDropDownMenu.getItem(index);
		final FeatureColor color = FeatureColor.getColor(selectedColor);

		for (int j = 0; j < featureListBuffer.size(); j++) {
			featureTable.getItem(j).setBackground(getItemColorFor(color));
		}

		newColor = color;
	}

	private void bufferSelectedFeatures() {
		featureListBuffer.clear();
		for (int i = 0; i < featureList.size(); i++) {
			featureListBuffer.add(featureList.get(i));
		}
	}

	/**
	 * Colors the background of the table items to show a preview of the changed colors
	 *
	 * @param featureTable
	 */
	private void colorPreview(final Table featureTable) {
		for (int i = 0; i < featureListBuffer.size(); i++) {
			final TableItem item = new TableItem(featureTable, SWT.NONE);
			item.setText(featureListBuffer.get(i).getName());

			final FeatureColor color = FeatureColor.getColor(colorDropDownMenu.getText());
			item.setBackground(getItemColorFor(color));
		}
	}

	/**
	 * @param parent
	 */
	@Override
	protected Control createContents(Composite parent) {
		super.createContents(parent);
		return parent;
	}

	@Override
	protected void okPressed() {
		final SetFeatureColorOperation op = new SetFeatureColorOperation(featureListBuffer.get(0).getFeatureModel(), featureListBuffer, newColor);

		if (enableUndoRedo) {
			try {
				PlatformUI.getWorkbench().getOperationSupport().getOperationHistory().execute(op, null, null);
			} catch (final ExecutionException e) {
				op.redo();
			}
		} else {
			op.redo();
		}

		super.okPressed();
	}

	public List<IFeature> getRecoloredFeatures() {
		return featureListBuffer;
	}

	private Color getItemColorFor(FeatureColor featureColor) {
		return featureColor == FeatureColor.NO_COLOR ? WHITE : ColorPalette.toSwtColor(featureColor);
	}
}
