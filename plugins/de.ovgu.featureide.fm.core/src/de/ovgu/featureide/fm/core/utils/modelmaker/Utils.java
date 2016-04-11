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
package de.ovgu.featureide.fm.core.utils.modelmaker;

import java.nio.file.Path;
import java.util.Collection;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

public class Utils {

    public static <E> String toString(final String label, final Collection<E> collection) {
        StringBuilder collectionString = new StringBuilder();
        collection.forEach((e) -> collectionString.append(e));
        return String.format("\"s\": [%s]", label, collectionString.toString());
    }

    public static <E> void requireNonEmpty(final E... resources) {
        if (resources.length == 0)
            throw new IllegalArgumentException();
    }

    public static void requireNonEmptyString(final String s) {
        if (s.trim().length() == 0)
            throw new IllegalArgumentException();
    }

    public static <K,V> void requireContainsKey(final Map<K, V> map, K key) {
        if (!map.containsKey(key))
            throw new NoSuchElementException();
    }

    public static String goPackageLevelUp(String packageName) {
        StringBuilder line = new StringBuilder(packageName);
        line = line.reverse();
        line = new StringBuilder(line.substring(line.indexOf(".") + 1)).reverse();
        return line.toString();
    }

    public static String getCurrentPackageIdentifier(String packageName) {
        StringBuilder line = new StringBuilder(packageName);
        line = line.reverse();
        line = new StringBuilder(line.substring(0, line.indexOf("."))).reverse();
        return line.toString();
    }

    public static String getFileExtension(String filename) {
        return getCurrentPackageIdentifier(filename);
    }

    public static boolean fileStartsWith(Set<String> filePrefixesBlackList, String filename) {
        for (String prefix : filePrefixesBlackList)
            if (filename.startsWith(prefix))
                return true;
        return false;
    }

    public static String getRelativeFilePath(String filePath, Path dir, String bundleRootFolder, String bundleFolder) {
        return filePath.substring(dir.toString().length() + 1 + bundleRootFolder.length() + 1 + bundleFolder.length() + 1);
    }

}