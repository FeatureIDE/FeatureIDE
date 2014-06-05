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

import java.util.List;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.AbstractSortModeNode;

/**
 * TreeNode who stores the number of used preprocessor directives, directives
 * per class and features per directives.<br>
 * This node should only be used for a preprocessor project.
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class DirectivesNode extends LazyParent {
	private FSTModel fstModel;

	/**
	 * Constructor for a {@code DirectivesNode}.
	 * 
	 * @param description
	 *            description of the node shown in the view
	 * @param fstModel
	 *            FSTModel for the calculation
	 */
	public DirectivesNode(String description, FSTModel fstModel) {
		super(description);
		this.fstModel = fstModel;
	}
	
	@Override
	protected void initChildren() {
		final Parent internClasses = new Parent("Classes");
		Parent project = new Parent("Project statistics");
		Integer maxNesting = 0;
		String maxNestingClass = null;
		
		project.addChild(new LazyParent("Number of directives") {
			@Override
			protected void initChildren() {
				new Aggregator().processAll(fstModel, this);
			}
		});
		
		Aggregator aggProject = new Aggregator();
		for (FSTClass clazz : fstModel.getClasses()) {
			String className;
			
			FSTRole role = clazz.getRoles().get(0);
			
			String packageName = role.getClassFragment().getPackage();
			String qualifiedPackageName = (packageName == null) ? "(default package)" : packageName;
			className = qualifiedPackageName + "." + role.getClassFragment().getName();
			
			Parent classNode = new Parent(className);
			aggProject.process(clazz.getRoles(), classNode);
			
			Integer currentNesting = aggProject.getMaxNesting();
			classNode.addChild(new Parent("Maximum nesting of directives", currentNesting));
			if (currentNesting > maxNesting) {
				maxNesting = currentNesting;
				maxNestingClass = className;
			}
			aggProject.setMaxNesting(0);
			
			internClasses.addChild(classNode);
		}
		
		Integer maximumSum = aggProject.getMaximumSum();
		Integer minimumSum = aggProject.getMinimumSum();
		
		Parent directivesPerClass = new Parent("Directives per class");
		directivesPerClass.addChild(new Parent("Maximum number of directives: " + maximumSum + " in class " + searchClass(internClasses.getChildren(), maximumSum)));
		directivesPerClass.addChild(new Parent("Minimum number of directives: " + minimumSum + " in class " + searchClass(internClasses.getChildren(), minimumSum)));
		directivesPerClass.addChild(new Parent("Average number of directives per class", getAverage(internClasses)));
		project.addChild(directivesPerClass);
		
		project.addChild(new LazyParent("Features per directive") {
			
			@Override
			protected void initChildren() {
				
				Aggregator aggregator = new Aggregator();
				
				aggregator.initializeDirectiveCount(fstModel);
				
				List<Integer> list = aggregator.getListOfNestings();
				double average = 0.0;
				for (Integer i : list) {
					average += i;
				}
				if (list.size() != 0) {
					average /= list.size();
					average *= 10;
					long rounded = Math.round(average);
					average = ((double) rounded) / 10;
				} else {
					average = 0.0;
				}
				
				addChild(new Parent("Maximum features per directive", aggregator.getMaxNesting()));
				addChild(new Parent("Minimum features per directive", aggregator.getMinNesting()));
				addChild(new Parent("Average features per directive", average));
			}
		});
		project.addChild(new Parent("Maximum nesting of directives: " + maxNesting + " in class " + maxNestingClass));
		
		addChild(project);
		
		Parent classes = new AbstractSortModeNode("Class statistics") {
			@Override
			protected void initChildren() {
				for (Parent child : internClasses.getChildren()) {
					addChild(child);
				}
			}
		};
		
		addChild(classes);
		
	}
	
	private String searchClass(Parent[] data, Integer input) {
		for (Parent p : data) {
			if (p.getValue().equals(input)) {
				String className = p.getDescription();
				return className;
			}
		}
		return null;
	}
	
	private Double getAverage(Parent parent) {
		if (parent.hasChildren()) {
			Integer numberOfDirectives = 0;
			for (Parent child : parent.getChildren()) {
				numberOfDirectives += (Integer) child.getValue();
			}
			
			Integer numberOfChildren = parent.getChildren().length;
			
			double average = numberOfDirectives;
			
			average /= (double) numberOfChildren;
			average *= 10;
			long rounded = Math.round(average);
			average = ((double) rounded) / 10;
			
			return average;
		}
		
		return 0.0;
	}
}