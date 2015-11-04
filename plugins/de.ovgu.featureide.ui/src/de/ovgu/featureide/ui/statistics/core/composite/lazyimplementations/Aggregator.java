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
import java.util.Collections;
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
	
	public static class AggregatorResult{
		private int nesting;
		private Map<String,Integer> directives = new HashMap<String, Integer>();
		
		public int getNesting() {
			return nesting;
		}
		public Map<String, Integer> getDirectives() {
			return directives;
		}
		public void setDirectives(Map<String, Integer> directives) {
			this.directives = directives;
		}
		public void setNesting(int nesting) {
			this.nesting = nesting;
		}		
		
	}
	
	//private Integer minimumSum;
	//private Integer maximumSum = 0;
	private Integer nestingCount = 0;
	private Integer maxNestingCount = 0;
	private int featureCount;
	private Integer maxNesting = 0;
	private Integer minNesting = 0;
	private List<Integer> nestings = new ArrayList<Integer>();
	private Map<String, AggregatorResult> class_to_directives = new HashMap<String,AggregatorResult>();
	
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

	private void calculateNestingCount(FSTDirective dir){
//		nestingCount++;
//		
//		for(FSTDirective child : dir.getChildren()){
//			calculateNestingCount(child);
//		}
//		if(nestingCount > maxNesting){
//			maxNesting = nestingCount;
//			nestingCount--;
//		}
		int level = 1;
		FSTDirective tmp = dir;
		while(tmp.getParent() != null){
			level++;
			tmp = tmp.getParent();
			
		}
		this.nestings.add(level);
		
		
	}
	
	/**
	 * Counts and groups all directives in the project.
	 * 
	 * @param fstModel
	 */
	private void initializeDirectiveCount(FSTModel fstModel) {
		this.featureCount = fstModel.getFeatures().size();
		for (FSTFeature feat : fstModel.getFeatures()) {
			for (FSTRole role : feat.getRoles()) {	
				this.nestings.clear();
				AggregatorResult result = this.class_to_directives.get(role.getFSTClass().getName());
				
				if(result == null)
					result = new AggregatorResult();
				
				Map<String,Integer> directives = result.getDirectives(); 
				for (FSTDirective dir : role.getDirectives()) {
					calculateNestingCount(dir);
					String identifier = role.getFSTClass().getName() + dir.getExpression() + dir.getEndLine();
					
					if (directives.containsKey(identifier)){
						int amount = directives.get(identifier);
						directives.put(identifier, amount + 1);
					}
					else
						directives.put(identifier, 1);
				}
				result.setNesting(Collections.max(this.nestings));
				result.setDirectives(directives);
				System.out.println(role.getFSTClass().getName() + " "+ result.getNesting());
				this.class_to_directives.put(role.getFSTClass().getName(), result);
			}
		}
		int i = 0;
		System.out.println(i);
	}
	
	public int getDirectiveCount(){
		int sum = 0;
		for(AggregatorResult values : this.class_to_directives.values())
			sum += values.getDirectives().size();
		
		return sum;
	}
	

	public Map.Entry<String,Integer> getMinimumNumberOfDirectives() {
		int minSum = Integer.MAX_VALUE;
		String className = "";
		
		for(Map.Entry<String,AggregatorResult> entry : this.class_to_directives.entrySet()){
			if(minSum > entry.getValue().getDirectives().size()){
				minSum =entry.getValue().getDirectives().size();
				className = entry.getKey();
			} 
		}
		
		return new AbstractMap.SimpleEntry<String,Integer>(className, minSum);
	}

	public Map.Entry<String,Integer> getMaximumNumberOfDirectives() {
		
		int maxSum = Integer.MIN_VALUE;
		String className = "";
		
		for(Map.Entry<String,AggregatorResult> entry : this.class_to_directives.entrySet()){
			if(maxSum < entry.getValue().getDirectives().size()){
				maxSum = entry.getValue().getDirectives().size();
				className = entry.getKey();
			} 
		}
		return new AbstractMap.SimpleEntry<String,Integer>(className, maxSum);
		
	}
	
	public Integer getDirectiveCountForClass(String className){
		
		AggregatorResult ret_val = class_to_directives.get(className);
		if(ret_val != null)
			return ret_val.getDirectives().size();
		else
			return 0;
				
	}
	
	public Integer getNestingCountForClass(String className){
		
		AggregatorResult ret_val = class_to_directives.get(className);
		if(ret_val != null)
			return ret_val.getNesting();
		else
			return 0;
	}
	
	public Map.Entry<String,Integer> getMaxNesting() {
		int maxSum = Integer.MIN_VALUE;
		String className = "";
		
		for(Map.Entry<String,AggregatorResult> entry : this.class_to_directives.entrySet()){
			if(maxSum < entry.getValue().getNesting()){
				maxSum = entry.getValue().getNesting();
				className = entry.getKey();
			} 
		}
		return new AbstractMap.SimpleEntry<String,Integer>(className, maxSum);
	}

	public Integer getMinNesting() {
		return minNesting;
	}

	public List<Integer> getListOfNestings() {
		return new ArrayList<Integer>();
	}

	/**
	 * @return
	 */
	public Double getAverageNumberOfDirectives() {
		
		int amount_classes = this.class_to_directives.size();
		int amount_directives = this.getDirectiveCount();
		
		double val = (double)amount_directives / (double) amount_classes;
		
		val = val*10;
		val = (double)((int) val);
		val = val /10;
		
		return val ;
	}

	/**
	 * @return
	 */
	public Integer getAverageNumberOfNestings() {
		//List<Integer> list = aggregator.getListOfNestings();
//		double average = 0.0;
//		for (Integer i : list) {
//			average += i;
//		}
//		if (list.size() != 0) {
//			average /= list.size();
//			average *= 10;
//			long rounded = Math.round(average);
//			average = ((double) rounded) / 10;
//		} else {
//			average = 0.0;
//		}
		return 10000;
	}

	/**
	 * @return
	 */
	public Map.Entry<String,Integer> getMaxNumberOfFeatures() {
		int maxNumber = Integer.MIN_VALUE;
		String className = "";
		
		for(Map.Entry<String, AggregatorResult> entry : this.class_to_directives.entrySet())
		{
			for(Map.Entry<String, Integer> innerentry : entry.getValue().getDirectives().entrySet())
			{
				if(maxNumber < innerentry.getValue()){
					maxNumber = innerentry.getValue();
					className = entry.getKey();
				} 
			}
		}
		return new AbstractMap.SimpleEntry<String,Integer>(className, maxNumber);
	}
	
	/**
	 * @return
	 */
	public Map.Entry<String,Integer> getMinNumberOfFeatures() {
		int maxNumber = Integer.MAX_VALUE;
		String className = "";
		
		for(Map.Entry<String, AggregatorResult> entry : this.class_to_directives.entrySet())
		{
			
			for(Map.Entry<String, Integer> innerentry : entry.getValue().getDirectives().entrySet())
			{
				if(maxNumber > innerentry.getValue()){
					maxNumber = innerentry.getValue();
					className = entry.getKey();
				} 
			}
		}
		return new AbstractMap.SimpleEntry<String,Integer>(className, maxNumber);
	}

	/**
	 * @return
	 */
	public Double getAverageNumberOfFeatures() {
		
		int sumFeaturePerDirectives = 0;
		for(Map.Entry<String, AggregatorResult> entry : this.class_to_directives.entrySet())
		{
			
			for(Map.Entry<String, Integer> innerentry : entry.getValue().getDirectives().entrySet())
			{
				sumFeaturePerDirectives += innerentry.getValue();
			}
		}
		
		double val = (double)sumFeaturePerDirectives / (double) this.getDirectiveCount();
		
		val = val*10;
		val = (double)((int) val);
		val = val /10;
		
		return val ;
	}

}
