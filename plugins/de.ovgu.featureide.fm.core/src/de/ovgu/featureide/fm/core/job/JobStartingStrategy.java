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

// @formatter:off
/**
 * Strategies for handling jobs that want to wait for other jobs to be finished first.<br/>
 * Possible strategies:<br/>
 * <pre>
 * {@link #RETURN}
 * {@link #WAIT}
 * {@link #WAIT_ONE}
 * {@link #CANCEL_WAIT}
 * {@link #CANCEL_WAIT_ONE}
 * </pre>
 *
 * @author Sebastian Krieter
 */
//@formatter:on
public enum JobStartingStrategy {
	/**
	 * If another job is already running the given job is not started.
	 */
	RETURN,

	/**
	 * Waits for all other jobs to finish.
	 */
	WAIT,

	/**
	 * Waits for another job to finish, except a third job is already waiting.
	 */
	WAIT_ONE,

	/**
	 * Same as {@link #WAIT}, but attempts to cancel all previous jobs.
	 */
	CANCEL_WAIT,

	/**
	 * Same as {@link #WAIT_ONE}, but attempts to cancel all previous jobs.
	 */
	CANCEL_WAIT_ONE
}
