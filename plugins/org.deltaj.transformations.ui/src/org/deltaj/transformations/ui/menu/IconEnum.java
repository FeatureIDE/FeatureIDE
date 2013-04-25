package org.deltaj.transformations.ui.menu;

import org.deltaj.transformations.ui.Activator;
import org.eclipse.jface.resource.ImageDescriptor;

public enum IconEnum {

	RESOLVE_MODIFY("resolve_modify.png"),
	RESOLVE_REMOVE("resolve_remove.png"),
	TRIANGLE("trianlge.png"),
	RENAME("rename.png"),
	REMOVE("remove.png"),
	REMOVE_DELTA("remove_delta.png"),
	REMOVE_FEATURE("remove_feature.png"),
	MERGE("merge.png"),
	CUT("cut.png"),
	CONFIGURATIONS("configurations.png");

	private final String filename;

	private IconEnum(String filename) {

		this.filename = filename;
	}

	public ImageDescriptor get() {

		return Activator.getIcon(filename);
	}
}
