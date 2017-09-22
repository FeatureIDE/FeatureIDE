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
package de.ovgu.featureide.fm.core.job;

/**
 * Interface for a stoppable job.
 *
 * @deprecated Use {@link LongRunningMethod} and {@link LongRunningWrapper} instead. <br/> A {@link IRunner} from the wrapper can be made stoppable via
 *             {@link IRunner#setStoppable(boolean)}.
 *
 * @author Sebastian Krieter
 */
@SuppressWarnings("rawtypes")
@Deprecated
public interface IStoppableJob extends IJob {

	int getCancelingTimeout();

	void setCancelingTimeout(int cancelingTimeout);
}
