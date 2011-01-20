/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.wizards;

import org.eclipse.swt.widgets.Composite;

/**
 * A dialog page for adding the FeatureIDE Nature.
 * TODO Jens, please revise this class
 * 
 * @author Jens Meinicke
 */
public class ConversionPage extends NewFeatureProjectPage {
	
	public ConversionPage(String project) {
		super();
		setDescription("Adds the FeatureIDE nature to the project" + project + ".");
	}

//	private Text backupPath;
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.wizards.NewFeatureProjectPage#createControl(org.eclipse.swt.widgets.Composite)
	 */
	@Override
	public void createControl(Composite parent) {
		super.createControl(parent);
//		String tooltip = "Sets the path of the backupfolder.";
//		Label label = new Label(pathGroup, SWT.NULL);
//		label.setText("&Backup Path:");
//		label.setToolTipText(tooltip);
//		backupPath = new Text(pathGroup, SWT.BORDER | SWT.SINGLE);
//		backupPath.setLayoutData(gd);
//		backupPath.setText("backup");
//		backupPath.setToolTipText(tooltip);
	}
	
//	public String getBackupPath() {
//		return backupPath.getText();
//	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.wizards.NewFeatureProjectPage#dialogChanged()
	 */
	@Override
	protected void dialogChanged() {
		super.dialogChanged();
//		if (getBackupPath().equals(getSourcePath())) {
//			updateStatus("Source Path equals Backup Path.");
//			return;
//		}
//		if (getBackupPath().equals(getBuildPath())) {
//			updateStatus("Build Path equals Backup Path.");
//			return;
//		}
//		if (getBackupPath().equals(getSourcePath())) {
//			updateStatus("Configurations Path equals Backup Path.");
//			return;
//		}
//		if (isPathEmpty(getBackupPath(), "Backup"))return;
//		
//		if (isInvalidPath(getBackupPath(), "Backup"))return;
	}
}
