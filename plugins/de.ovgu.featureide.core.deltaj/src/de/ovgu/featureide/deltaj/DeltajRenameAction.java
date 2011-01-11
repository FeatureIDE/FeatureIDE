package de.ovgu.featureide.deltaj;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.fm.core.IRenameAction;
/**
 * 
 * 
 *  
 * @author Fabian Benduhn
*/
public class DeltajRenameAction implements IRenameAction {

	@Override
	public void
			performRenaming(String oldName, String newName, IProject project) {
		//do nothing 
		//only implemented because we do not want to create feature folders
		
	}

}
