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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class Exporter {

    Set<String> declaredFeatures = new HashSet<>();

    static class Keywords {
        static final String UNRESOLVED = "unresolved";
        static final String PROJECT = "project";
        static final String FEATURE = "feature";
        static final String REQUIRES = "requires";
        static final String PARENT_OF = "parent_of";
    }

    //List<String> lines = new LinkedList<>();

    public static class Content {
        public List<String> unresolved;
        public List<String> project;
        public List<String> feature;
        public List<Pair<String>> requires;
        public List<Pair<String>> parentof;
    }

    Set<String> unresolved = new HashSet<>();
    Set<String> project = new HashSet<>();
    Set<String> feature= new HashSet<>();
    Set<Pair<String>> requires = new HashSet<>();
    Set<Pair<String>> parentof= new HashSet<>();

    public void clear() {
        unresolved.clear();
        project.clear();
        feature.clear();
        requires.clear();
        parentof.clear();

        unresolvedFeatures.clear();
        declaredFeatures.clear();
    }

    Set<String> unresolvedFeatures = new HashSet<>();

    public Content getContent() {
        Content result = new Content();
        
        result.unresolved = new ArrayList<>();
        for (String unresolved : distinct_sort(unresolvedFeatures)) {
        	final String featureName = unresolved.startsWith("package:")? unresolved : (unresolved.startsWith("class:") ? unresolved : ("class:"+unresolved));
        	result.unresolved.add(featureName);
        }
        
        result.project = Collections.unmodifiableList(distinct_sort(project));
        result.feature = Collections.unmodifiableList(distinct_sort(declaredFeatures));
        result.requires = Collections.unmodifiableList(distinct_sort(requires));
        result.parentof = Collections.unmodifiableList(distinct_sort(parentof));

        return result;
    }

    private <T extends Comparable> List<? extends T> distinct_sort(Set<T> set) {
        List<T> list = new ArrayList<>(set);
        Collections.sort(list);
        return list;
    }

    public void project(String projectName) {
        project.add(projectName);
    }


    public void parent_of(String projectName, String bundle) {
        projectName = projectName.toLowerCase();
        bundle = bundle.toLowerCase();

        parentof.add(new Pair<String>(projectName, bundle));
    }

    public static class Pair<T extends Comparable<T>> implements Comparable<T> {
        public T first, second;
        public Pair(T first, T second) {
            this.first = first;
            this.second = second;
        }

        @Override
        public String toString() {
            return first + ";" + second;
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;

            Pair<?> pair = (Pair<?>) o;

            if (first != null ? !first.equals(pair.first) : pair.first != null) return false;
            return second != null ? second.equals(pair.second) : pair.second == null;

        }

        @Override
        public int hashCode() {
            int result = first != null ? first.hashCode() : 0;
            result = 31 * result + (second != null ? second.hashCode() : 0);
            return result;
        }

        @Override
        public int compareTo(T o) {
            Pair<T> t = (Pair<T>) o;
            return first.compareTo(t.first) < 0 ? -1 : (first.compareTo(t.first) > 0 ? +1 : second.compareTo(t.second));
        }
    }

    public void feature(String feature) {
        feature = feature.toLowerCase();

        unresolvedFeatures.remove(feature);
        declaredFeatures.add(feature);
    }

    public void requires(String featureA, String featureB) {
        featureA = featureA.toLowerCase();
        featureB = featureB.toLowerCase();

        requires.add(new Pair<>(featureA, featureB));
        if (!declaredFeatures.contains(featureA))
            unresolvedFeatures.add(featureA);
        if (!declaredFeatures.contains(featureB))
            unresolvedFeatures.add(featureB);
    }
}