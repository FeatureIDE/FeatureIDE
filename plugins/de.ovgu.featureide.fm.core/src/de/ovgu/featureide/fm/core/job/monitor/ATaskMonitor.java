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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.job.monitor;

/**
 *
 * @author Sebastian Krieter
 */
abstract class ATaskMonitor extends AMonitor {

	protected String name = null;

	public ATaskMonitor() {
		super();
	}

	public ATaskMonitor(String name) {
		super();
		this.name = name;
	}

	protected ATaskMonitor(AMonitor parent) {
		super(parent);
	}

	@Override
	public void setTaskName(String name) {
		this.name = name;
	}

	@Override
	public String getTaskName() {
		return constructTaskName();
	}

	protected String constructTaskName() {
		final StringBuilder sb = new StringBuilder();
		AMonitor p = parent;
		while (p != null) {
			sb.append(p.getTaskName());
			sb.append(" - ");
			p = p.parent;
		}
		sb.append(name != null ? name : "...");
		return sb.toString();
	}

}
