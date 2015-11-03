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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import static de.ovgu.featureide.fm.core.localization.StringTable.DIRECTIVES;
import static de.ovgu.featureide.fm.core.localization.StringTable.NUMBER_OF;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirectiveCommand;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Evaluates minimum- and maximum- values for a set of directives.
 * 
 * @see DirectivesNode
 * 
 * @author Christopher Kruczek
 * @author Andy Kenner
 * @author Dominik Hamann
 * @author Patrick Haese
 * 
 */
public class Aggregator {
	
	private Integer minimumSum;
	private Integer maximumSum = 0;
	private Integer nestingCount = 0;
	private Integer maxNesting = 0;
	private Integer minNesting = null;
	private Map<String,Set<String>> class_to_directives = new HashMap();
	private int curNestingCount = 0;

	

//	/**
//	 * Processes one set of directives and adds the result to the given parent.
//	 * 
//	 * @param roles
//	 * @param parent
//	 */
//	public void process(List<FSTRole> roles, Parent parent) {
//		DirectiveMap classcount = new DirectiveMap();
//		for (FSTRole role : roles) {
//			for (FSTDirective dir : role.getDirectives()) {
//				classcount.add(dir);
//				if (maxNesting < nestingCount) {
//					maxNesting = nestingCount;
//				}
//				nestingCount = 0;
//			}
//		}
//		handleExtremes(classcount);
//		mapToChild(parent, classcount);
//		parent.setValue(sum(classcount));
//	}

	/**
	 * Counts and groups all directives in the project and adds the information
	 * to the given node.
	 * 
	 * @param fstModel
	 * @param parent
	 */
	public void processAll(FSTModel fstModel) {
		initializeDirectiveCount(fstModel);
	}

	/**
	 * Counts and groups all directives in the project.
	 * 
	 * @param fstModel
	 */
	private void initializeDirectiveCount(FSTModel fstModel) {
		int sumDirectives = 0;
		
		for (FSTFeature feat : fstModel.getFeatures()) {
			for (FSTRole role : feat.getRoles()) {		
				Set<String> directives = new HashSet();
				for (FSTDirective dir : role.getDirectives()) {
					String identifier = role.getFSTClass().getName() + dir.getExpression() + dir.getEndLine();
					directives.add(identifier);
//					directiveCount.add(dir);
//					if (maxNesting < nestingCount) {
//						maxNesting = nestingCount;
//					}
//					if (minNesting == null) {
//						minNesting = nestingCount;
//					} else if (minNesting > nestingCount) {
//						minNesting = nestingCount;
//					}
//					listOfNestings.add(nestingCount);
//					nestingCount = 0;
				}
				Set<String> tmp = this.class_to_directives.getOrDefault(role.getFSTClass().getName(), new HashSet());
				tmp.addAll(directives);
				this.class_to_directives.put(role.getFSTClass().getName(), tmp);
			}
				
		}
		
		int i = 0;
	}

	
	public int getDirectiveCount(){
		int sum = 0;
		for(Set s : this.class_to_directives.values())
			sum += s.size();
		
		return sum;
	}
	

	public Map.Entry getMinimumNumberOfDirectives() {
		int minSum = Integer.MAX_VALUE;
		String className = "";
		
		for(Map.Entry<String,Set<String>> entry : this.class_to_directives.entrySet()){
			if(minSum > entry.getValue().size()){
				minSum =entry.getValue().size();
				className = entry.getKey();
			} 
		}
		
		return new AbstractMap.SimpleEntry<String,Integer>(className, minSum);
	}

	public Map.Entry getMaximumNumberOfDirectives() {
		
		int maxSum = Integer.MIN_VALUE;
		String className = "";
		
		for(Map.Entry<String,Set<String>> entry : this.class_to_directives.entrySet()){
			if(maxSum < entry.getValue().size()){
				maxSum = entry.getValue().size();
				className = entry.getKey();
			} 
		}
		return new AbstractMap.SimpleEntry<String,Integer>(className, maxSum);
		
	}
	
	public Integer getDirectiveCountForClass(String className){
		return class_to_directives.getOrDefault(className, new HashSet()).size();
	}
	
	public Integer getMaxNesting() {
		return maxNesting;
	}

	public Integer getMinNesting() {
		return minNesting;
	}

	public List<Integer> getListOfNestings() {
		return new ArrayList();
	}

	public void setMaxNesting(Integer maxNesting) {
		this.maxNesting = maxNesting;
	}

//	private void handleExtremes(DirectiveMap newInput) {
//		Integer sum = sum(newInput);
//		if (sum != 0) {
//			if (minimumSum == null) {
//				minimumSum = sum;
//			} else {
//				minimumSum = sum < minimumSum ? sum : minimumSum;
//			}
//			maximumSum = sum > maximumSum ? sum : maximumSum;
//		}
//	}

//	private Integer sum(DirectiveMap newInput) {
//		Integer sum = 0;
//		for (Integer value : newInput.values()) {
//			sum += value;
//		}
//		return sum;
//	}
}
