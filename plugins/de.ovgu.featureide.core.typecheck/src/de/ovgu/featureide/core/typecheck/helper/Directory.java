/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.core.typecheck.helper;

import java.io.File;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * TODO description
 * 
 * @author soenke
 */
public class Directory {
	private File directory;

	private Map<File, Long> times;

	/**
	 * 
	 */
	public Directory(File dir) {
		directory = dir;

		init();
	}

	public boolean changed() {
		Set<File> current_files = parse();
		if (current_files.size() != times.keySet().size()) {
			return true;
		}

		for (File f : current_files) {
			if (times.containsKey(f)) {
				if (times.get(f) != f.lastModified()) {
					return true;
				}
			} else {
				return true;
			}
		}

		return false;
	}

	private void init() {
		times = new HashMap<File, Long>();

		for (File f : parse()) {
			times.put(f, 0l);
		}
	}

	public void update() {
		times = new HashMap<File, Long>();

		for (File f : parse()) {
			times.put(f, f.lastModified());
		}
	}

	private Set<File> parse() {
		return parse(directory);
	}

	private Set<File> parse(File f) {
		Set<File> set = new HashSet<File>();

		if (f.isFile()) {
			if (f.getName().endsWith(".java")) {
				set.add(f);
			}
		} else {
			for (File c : f.listFiles()) {
				set.addAll(parse(c));
			}
		}
		return set;
	}

}
