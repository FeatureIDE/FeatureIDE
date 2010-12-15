package de.ovgu.featureide.fm.core;

import org.eclipse.core.resources.IProject;

/**
 * 
 * ExtensionPoint for composer specific renamings
 * 
 * @author Jens Meinicke
 */
public interface IRenameAction {
	
	/**
	 * Perform renaming after rename some features at feature model
	 * @param oldName
	 * @param newName
	 * @param project
	 */
	public void performRenaming(String oldName, String newName, IProject project);
}
