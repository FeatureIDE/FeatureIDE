/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base.event;

import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * Default implementation of {@link IEventManager}.
 * 
 * @author Sebastian Krieter
 */
public class DefaultEventManager implements IEventManager, IEventListener {

	protected final List<IEventListener> listenerList = new LinkedList<>();

	@Override
	public void addListener(IEventListener listener) {
		if (!listenerList.contains(listener)) {
			listenerList.add(listener);
		}
	}

	@Override
	public void fireEvent(FeatureIDEEvent event) {
		if (event.isPersistent() || event.getEditor() == null) {
			for (final IEventListener listener : listenerList) {
				callListener(event, listener);
			}
		} else {
			final int listenerIndex = listenerList.indexOf(event.getEditor());
			if (listenerIndex >= 0) {
				callListener(event, listenerList.get(listenerIndex));
			}
		}
	}

	protected void callListener(FeatureIDEEvent event, final IEventListener listener) {
		try {
			listener.propertyChange(event);
		} catch (Throwable e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public void removeListener(IEventListener listener) {
		listenerList.remove(listener);
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		fireEvent(event);
	}

}
