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
package featureide.fm.ui.editors.featuremodel.commands;

import org.eclipse.gef.commands.Command;

import featureide.fm.core.FeatureModel;

/**
 * Renames a currently selected feature.
 * 
 * @author Thomas Thuem
 */
public class FeatureRenamingCommand extends Command {
	
	private final FeatureModel featureModel;

	private final String oldName;
	
	private final String newName;

	public FeatureRenamingCommand(FeatureModel featureModel, String oldName, String newName) {
		super("Renaming feature " + oldName);
		this.featureModel = featureModel;
		this.oldName = oldName;
		this.newName = newName;
	}
	
	@Override
	public boolean canExecute() {
		if (newName == null)
			return false;
		if (featureModel.getFeatureNames().contains(newName))
			return false;
		return isValidJavaIdentifier(newName);
	}
	
	@Override
	public void execute() {
		featureModel.renameFeature(oldName, newName);
		featureModel.handleModelDataChanged();
	}
	
	@Override
	public void undo() {
		featureModel.renameFeature(newName, oldName);
		featureModel.handleModelDataChanged();
	}
	
	public static boolean isValidJavaIdentifier(String s) {
		if (s == null)
			return false;
		final int len = s.length();
		if (len == 0 || !Character.isJavaIdentifierStart(s.charAt(0)))
			return false;
		for (int i = 1; i < len; i++) {
			if (!Character.isJavaIdentifierPart(s.charAt(i)))
				return false;
		}
		return true;
	}

}
