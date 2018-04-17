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
package de.ovgu.featureide.fm.ui.editors.featuremodel.commands.renaming;

import static de.ovgu.featureide.fm.core.localization.StringTable.INVALID_NAME;
import static de.ovgu.featureide.fm.core.localization.StringTable.IT_IS_NOT_RECOMMENDED_TO_CHANGE_UPPER_AND_LOWER_CASE__YOU_CURRENTLY_TRY_TO_RENAME;
import static de.ovgu.featureide.fm.core.localization.StringTable.THIS_NAME_IS_ALREADY_USED_FOR_ANOTHER_FEATURE_;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.gef.tools.DirectEditManager;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ICellEditorListener;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.ToolTip;

import de.ovgu.featureide.fm.core.FMComposerManager;
import de.ovgu.featureide.fm.core.IFMComposerExtension;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * Initializes the cell editor for feature renamings and adds a listener to show a tooltip if the current name is not allowed.
 *
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 * @author Marcus Pinnecke
 */
public class FeatureLabelEditManager extends DirectEditManager implements GUIDefaults {

	private final IFeatureModel featureModel;

	public FeatureLabelEditManager(FeatureEditPart editpart, Class<?> editorType, FeatureCellEditorLocator locator, IFeatureModel featureModel) {
		super(editpart, editorType, locator);
		this.featureModel = featureModel;
	}

	@Override
	protected void initCellEditor() {
		final CellEditor cellEditor = getCellEditor();
		final Control control = cellEditor.getControl();
		final String oldValue = ((FeatureEditPart) getEditPart()).getModel().getObject().getName();

		control.setFont(DEFAULT_FONT);
		cellEditor.setValue(oldValue);

		cellEditor.addListener(new ICellEditorListener() {

			private ToolTip tooltip;

			@Override
			public void editorValueChanged(boolean oldValidState, boolean newValidState) {
				closeTooltip();
				final String value = (String) cellEditor.getValue();
				if (!value.equals(oldValue)) {
					if (value.equalsIgnoreCase(oldValue)) {
						createTooltip(IT_IS_NOT_RECOMMENDED_TO_CHANGE_UPPER_AND_LOWER_CASE__YOU_CURRENTLY_TRY_TO_RENAME + oldValue + " to " + value + ".",
								SWT.ICON_WARNING);
						// TODO #455 wrong usage of extension
					} else {
						final IProject project =
							ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(new Path(featureModel.getSourceFile().toString())).getProject();
						final IFMComposerExtension fmComposerExtension = FMComposerManager.getFMComposerExtension(project);
						if ((!fmComposerExtension.isValidFeatureName(value))) {
							createTooltip(fmComposerExtension.getErrorMessage(), SWT.ICON_ERROR);
						} else if (Functional.toList(FeatureUtils.extractFeatureNames(featureModel.getFeatures())).contains(value)) {
							createTooltip(THIS_NAME_IS_ALREADY_USED_FOR_ANOTHER_FEATURE_, SWT.ICON_ERROR);
						}
					}
				}
			}

			@Override
			public void cancelEditor() {
				closeTooltip();
			}

			@Override
			public void applyEditorValue() {
				closeTooltip();
			}

			private void createTooltip(String message, int icon) {
				tooltip = new ToolTip(control.getShell(), SWT.BALLOON | icon);
				tooltip.setAutoHide(false);
				tooltip.setLocation(control.toDisplay(control.getSize().x / 2, control.getSize().y + 5));
				tooltip.setText(INVALID_NAME);
				tooltip.setMessage(message);
				tooltip.setVisible(true);
			}

			private void closeTooltip() {
				if (tooltip != null) {
					tooltip.setVisible(false);
					tooltip = null;
				}
			}
		});
	}

}
