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
package de.ovgu.featureide.refactoring.windows;

import java.net.URI;

/**
 * A general refactoring dialog.
 * 
 * @author Stephan Kauschka
 */
public interface Window {

    public static final int ERROR_TEXT = 1;
    public static final int METHOD_TEXT = 2;
    public static final int LAYER_TEXT = 3;

    public void setText(int component, String text);

    public URI getProjectURI();

}
