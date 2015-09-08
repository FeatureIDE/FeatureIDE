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
public class ProgressLogger {

	private final ProgressTimer timer = new ProgressTimer();
	
	public void log(String message) {
		log(message, false);
	}
	
	public void log(String message, boolean linebreak) {
		if (timer.isRunning()) {
			timer.split();
		} else {
			timer.start();
		}
		if (linebreak) {
			System.out.println(message);
		} else {
			System.out.print(message);
		}
	}
	
	public void stop() {
		timer.stop();
	}
	
	public void finish() {
		timer.split();
		System.out.println();
		System.out.println(" > Done!");
		System.out.print("Global Time");
		timer.stop();
	}

}
