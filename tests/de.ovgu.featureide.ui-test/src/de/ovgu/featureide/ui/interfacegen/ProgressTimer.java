/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.interfacegen;

/**
 * @author Sebastian Krieter
 */
public class ProgressTimer {

	private boolean running = false;
	private boolean verbose = true;

	private long startTime;

	private long curTime = 0;

	private long lastTime = -1;

	public void start() {
		startTime = System.nanoTime();
		curTime = startTime;
		running = true;
	}

	public long stop() {
		lastTime = System.nanoTime() - startTime;

		if (verbose) {
			final double timeDiff = Math.floor(lastTime / 1000000.0) / 1000.0;
			System.out.println(" -> " + timeDiff + "s");
		}

		running = false;
		return lastTime;
	}

	public long split() {
		final long startTime = curTime;
		curTime = System.nanoTime();

		lastTime = System.nanoTime() - startTime;

		if (verbose) {
			final double timeDiff = Math.floor(lastTime / 1000000.0) / 1000.0;
			System.out.println(" -> " + timeDiff + "s");
		}

		return lastTime;
	}

	public final boolean isRunning() {
		return running;
	}

	public long getLastTime() {
		return lastTime;
	}

	public boolean isVerbose() {
		return verbose;
	}

	public void setVerbose(boolean verbose) {
		this.verbose = verbose;
	}

}
