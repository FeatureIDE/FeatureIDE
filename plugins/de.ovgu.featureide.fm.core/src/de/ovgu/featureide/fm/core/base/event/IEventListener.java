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
package de.ovgu.featureide.fm.core.base.event;

import de.ovgu.featureide.fm.core.base.impl.FeatureModel;

/**
 * Interface for components listening to events fired by other components. <br/> Some classes of FeatureIDE use the observer-pattern, to notify listening
 * clients. For instance, a feature model fires a "model data changed" event when the model is changed. Listening clients, e.g., the diagram editor can react on
 * this event. <br/> <br/> The follow sketch outlines the observer-pattern usage in FeatureIDE, taken
 * {@link de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor} and {@link FeatureModel} as example. <code><pre> IEventListener <--- propertyChange is called
 * --------- | | | | implements fires event | | V | FeatureDiagramEditor -- register as listener ---> FeatureModel </pre></code> An instance of
 * <code>FeatureMode</code> expects instances of <code>IEventListener</code> as listeners. Since <code>FeatureDiagramEditor</code> is instance of
 * </code>IEventListener</code>, it can be passed to the instance of <code>FeatureModel</code>. When a change in the data occurs, the instance of
 * <code>FeatureModel</code> will notify all attached <code>IEventListener</code> instances and, hence, the instance of <code>FeatureDiagramEditor</code>. <br/>
 * <br/> Please note that events fired and received over this interface are from type {@link FeatureIDEEvent}.
 *
 * @author Sebastian Krieter
 */
public interface IEventListener {

	/**
	 * This method is called whenever the
	 *
	 * @param event
	 */
	void propertyChange(FeatureIDEEvent event);

}
