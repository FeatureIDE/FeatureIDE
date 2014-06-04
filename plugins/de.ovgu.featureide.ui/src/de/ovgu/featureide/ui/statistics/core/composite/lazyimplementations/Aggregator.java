/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

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
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class Aggregator {
	private Integer minimumSum;
	private Integer maximumSum = 0;
	private Integer nestingCount = 0;
	private Integer maxNesting = 0;
	private Integer minNesting = null;
	private List<Integer> listOfNestings = new LinkedList<Integer>();

	private Integer blub = 0;

	private DirectiveMap directiveCount = new DirectiveMap();

	/**
	 * 
	 * Convenience-class for evaluating sets of directives without having to use
	 * the diamond-operator everytime. Also offers a method for counting the
	 * directives.
	 * 
	 * @author Dominik Hamann
	 * @author Haese Patrick
	 */
	class DirectiveMap extends HashMap<FSTDirectiveCommand, Integer> {

		private static final long serialVersionUID = -1724069966296918497L;

		/**
		 * Counts directives by recursively checking them.
		 * 
		 * @param dir
		 */
		public void add(FSTDirective dir) {
			nestingCount++;
			FSTDirectiveCommand com = dir.getCommand();
			put(com, containsKey(com) ? get(com) + 1 : 1);
			if (dir.hasChildren()) {
				for (FSTDirective child : dir.getChildrenList()) {
					this.add(child);
				}
			} else {
				if (blub < nestingCount) {
					int temp = blub;
					blub = nestingCount;
					nestingCount -= temp;
				}
			}
		}
	}

	/**
	 * Processes one set of directives and adds the result to the given parent.
	 * 
	 * @param roles
	 * @param parent
	 */
	public void process(List<FSTRole> roles, Parent parent) {
		DirectiveMap classcount = new DirectiveMap();
		for (FSTRole role : roles) {
			for (FSTDirective dir : role.getDirectives()) {
				classcount.add(dir);
				if (maxNesting < nestingCount) {
					maxNesting = nestingCount;
				}
				nestingCount = 0;
			}
		}
		handleExtremes(classcount);
		mapToChild(parent, classcount);
		parent.setValue(sum(classcount));
	}

	/**
	 * Counts and groups all directives in the project and adds the information
	 * to the given node.
	 * 
	 * @param fstModel
	 * @param parent
	 */
	public void processAll(FSTModel fstModel, Parent parent) {
		initializeDirectiveCount(fstModel);
		mapToChild(parent, directiveCount);
		parent.setValue(sum(directiveCount));
	}

	/**
	 * Counts and groups all directives in the project.
	 * 
	 * @param fstModel
	 */
	public void initializeDirectiveCount(FSTModel fstModel) {
		for (FSTFeature feat : fstModel.getFeatures()) {
			for (FSTRole role : feat.getRoles()) {
				for (FSTDirective dir : role.getDirectives()) {
					directiveCount.add(dir);
					if (maxNesting < nestingCount) {
						maxNesting = nestingCount;
					}
					if (minNesting == null) {
						minNesting = nestingCount;
					} else if (minNesting > nestingCount) {
						minNesting = nestingCount;
					}
					listOfNestings.add(nestingCount);
					nestingCount = 0;
				}
			}
		}
	}

	private void mapToChild(Parent parent, DirectiveMap count) {
		for (FSTDirectiveCommand com : FSTDirectiveCommand.values()) {
			if (count.containsKey(com)) {
				parent.addChild(new Parent("Number of " + com.toString()
						+ " directives", count.get(com)));
			}
		}
	}

	public DirectiveMap getDirectiveCount() {
		return directiveCount;
	}

	public Integer getMinimumSum() {
		return minimumSum;
	}

	public Integer getMaximumSum() {
		return maximumSum;
	}

	public Integer getMaxNesting() {
		return maxNesting;
	}

	public Integer getMinNesting() {
		return minNesting;
	}

	public List<Integer> getListOfNestings() {
		return listOfNestings;
	}

	public void setMaxNesting(Integer maxNesting) {
		this.maxNesting = maxNesting;
	}

	private void handleExtremes(DirectiveMap newInput) {
		Integer sum = sum(newInput);
		if (sum != 0) {
			if (minimumSum == null) {
				minimumSum = sum;
			} else {
				minimumSum = sum < minimumSum ? sum : minimumSum;
			}
			maximumSum = sum > maximumSum ? sum : maximumSum;
		}
	}

	private Integer sum(DirectiveMap newInput) {
		Integer sum = 0;
		for (Integer value : newInput.values()) {
			sum += value;
		}
		return sum;
	}
}