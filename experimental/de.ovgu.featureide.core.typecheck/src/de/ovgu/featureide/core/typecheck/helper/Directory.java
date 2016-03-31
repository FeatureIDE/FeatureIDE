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
package de.ovgu.featureide.core.typecheck.helper;

import java.io.File;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Auxiliary class to detect file changes in a given directory and its sub
 * directories
 * 
 * @author Soenke Holthussen
 */
public class Directory {
    /**
     * The directory to watch
     */
    private File directory;

    /**
     * The recorded times of the last modification of the files at the last
     * iteration
     */
    private Map<File, Long> times;

    /**
     * Set the directory, update the modification times
     * 
     * @param dir
     */
    public Directory(File dir) {
	directory = dir;

	update();
    }

    /**
     * Checks if a file in the directory or its sub-directories was changed
     * 
     * @return true if a file was changed, false otherwise
     */
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

    /**
     * updates the modification times
     */
    public void update() {
	times = new HashMap<File, Long>();

	for (File f : parse()) {
	    times.put(f, f.lastModified());
	}
    }

    private Set<File> parse() {
	return parse(directory);
    }

    /**
     * iterates through a directory, searching for .java files
     * 
     * @param directory
     *            to search through
     * @return a set of .java files in the given directory and its
     *         sub-directories
     */
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
