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
package de.ovgu.featureide.core.mpl.builder;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectNature;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.mpl.MPLPlugin;

/**
 * Nature of an interface project.
 *
 * @author Sebastian Krieter
 */
public class InterfaceProjectNature implements IProjectNature {

	public static final String NATURE_ID = MPLPlugin.PLUGIN_ID + ".interfaceProjectNature";

	private IProject project;

	@Override
	public void configure() throws CoreException {
//		IProjectDescription desc = project.getDescription();
//		ICommand[] commands = desc.getBuildSpec();
//
//		for (int i = 0; i < commands.length; ++i) {
//			if (commands[i].getBuilderName().equals(InterfaceProjectBuilder.BUILDER_ID)) {
//				return;
//			}
//		}
//
//		ICommand[] newCommands = new ICommand[commands.length + 1];
//		System.arraycopy(commands, 0, newCommands, 1, commands.length);
//		ICommand command = desc.newCommand();
//		command.setBuilderName(InterfaceProjectBuilder.BUILDER_ID);
//		newCommands[0] = command;
//		desc.setBuildSpec(newCommands);
//		project.setDescription(desc, null);
	}

	@Override
	public void deconfigure() throws CoreException {}

	@Override
	public IProject getProject() {
		return project;
	}

	@Override
	public void setProject(IProject project) {
		this.project = project;
	}

}
