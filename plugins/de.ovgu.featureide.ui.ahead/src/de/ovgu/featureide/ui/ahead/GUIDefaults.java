/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.ui.ahead;

import org.eclipse.swt.graphics.Image;

/**
 * Default images for the ahead.ui plug-in.
 * 
 * @author Jens Meinicke
 */
public interface GUIDefaults {
	/*
	 * All images should be declared here, so an image can not be created twice.
	 */
	public final static Image IMAGE_FIELD_PRIVATE = AheadUIPlugin.getImage("field_private_obj.gif");
	public final static Image IMAGE_FIELD_PROTECTED = AheadUIPlugin.getImage("field_protected_obj.gif");
	public final static Image IMAGE_FIELD_PUBLIC = AheadUIPlugin.getImage("field_public_obj.gif");
	public final static Image IMAGE_FIELD_DEFAULT = AheadUIPlugin.getImage("field_default_obj.gif");
	public final static Image IMAGE_METHODE_PRIVATE = AheadUIPlugin.getImage("private_co.gif");
	public final static Image IMAGE_METHODE_PROTECTED = AheadUIPlugin.getImage("protected_co.gif");
	public final static Image IMAGE_METHODE_PUBLIC = AheadUIPlugin.getImage("public_co.gif");
	public final static Image IMAGE_METHODE_DEFAULT =  AheadUIPlugin.getImage("default_co.gif");
	public final static Image IMAGE_CLASS = AheadUIPlugin.getImage("class_obj.gif");

	public final static Image IMAGE_JAK_FILE = AheadUIPlugin.getImage("JakFileSmall.png");
}
