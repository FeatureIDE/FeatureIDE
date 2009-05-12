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
package featureide.fm.ui.editors.featuremodel.commands.renaming;

import org.eclipse.gef.tools.DirectEditManager;
import org.eclipse.jface.viewers.CellEditor;
import org.eclipse.jface.viewers.ICellEditorListener;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.ToolTip;

import featureide.fm.core.FeatureModel;
import featureide.fm.ui.editors.featuremodel.GUIDefaults;
import featureide.fm.ui.editors.featuremodel.commands.FeatureRenamingCommand;
import featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * Initializes the cell editor for feature renamings and adds a listener to show
 * a tooltip if the current name is not allowed.
 * 
 * @author Thomas Thuem
 */
public class FeatureLabelEditManager extends DirectEditManager implements GUIDefaults {

	private FeatureModel featureModel;

	@SuppressWarnings("unchecked")
	public FeatureLabelEditManager(FeatureEditPart editpart, Class editorType, 
			FeatureCellEditorLocator locator, FeatureModel featureModel) {
		super(editpart, editorType, locator);
		this.featureModel = featureModel;
	}

	@Override
	protected void initCellEditor() {
		final CellEditor cellEditor = getCellEditor();
		final Control control = cellEditor.getControl();
		final String oldValue = ((FeatureEditPart) getEditPart()).getFeatureModel().getName();
		
		control.setFont(DEFAULT_FONT);
		cellEditor.setValue(oldValue);
		
		cellEditor.addListener(new ICellEditorListener() {
			private ToolTip tooltip;
			@Override
			public void editorValueChanged(boolean oldValidState, boolean newValidState) {
				closeTooltip();
				String value = (String) cellEditor.getValue();
				if (!value.equals(oldValue)) {
					if (value.equalsIgnoreCase(oldValue))
						createTooltip("It is not recommended to change upper and lower case. You currently try to rename " + oldValue + " to " + value + ".", SWT.ICON_WARNING);
					else if (!FeatureRenamingCommand.isValidJavaIdentifier(value))
						createTooltip("The name need to be a valid Java identifier.", SWT.ICON_ERROR);
					else if (featureModel.getFeatureNames().contains(value))
						createTooltip("This name is already used for another feature.", SWT.ICON_ERROR);
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
				tooltip.setLocation(control.toDisplay(control.getSize().x/2, control.getSize().y + 5));
				tooltip.setText("Invalid Name");
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
