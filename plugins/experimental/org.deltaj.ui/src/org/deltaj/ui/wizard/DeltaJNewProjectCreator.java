/**
 * 
 */
package org.deltaj.ui.wizard;

import java.util.List;

import org.deltaj.generator.DeltaJBuilder;

import com.google.common.collect.ImmutableList;

/**
 * @author bettini
 * 
 */
public class DeltaJNewProjectCreator extends DeltaJProjectCreator {

	protected final List<String> DELTAJ_SRC_FOLDER_LIST = ImmutableList.of(SRC_ROOT,
			DeltaJBuilder.DELTAJ_GEN_DIRECTORY);

	@Override
	protected List<String> getAllFolders() {
		return DELTAJ_SRC_FOLDER_LIST;
	}
}
