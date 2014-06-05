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
package de.ovgu.featureide.fm.core.editing.evaluation;

import java.util.LinkedList;
import java.util.List;
import java.util.Random;

import org.prop4j.And;
import org.prop4j.AtMost;
import org.prop4j.Equals;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * A generator for feature models.
 * 
 * @author Thomas Thüm
 */
public abstract class Generator {
	
	public static final int TIMEOUT = 60;
	
	public final static int maxChildren = 10;
	
	public final static int minLiterals = 2;
	public final static int maxLiterals = 5;
	
	public static FeatureModel generateFeatureModel(long id, int numberOfFeatures) {
		Random random = new Random(id);
		FeatureModel fm = generateFeatureDiagram(random, numberOfFeatures);
		generateConstraints(fm, random, numberOfFeatures / 10);
		return fm;
	}
	
	public static FeatureModel generateFeatureDiagram(Random random, int numberOfFeatures) {
		FeatureModel fm = new FeatureModel();
		List<Feature> leaves = new LinkedList<Feature>();
		leaves.add(fm.getFeature("C1"));
		int count = 1;
		while (count < numberOfFeatures) {
			int parentIndex = random.nextInt(leaves.size());
			Feature parent = leaves.remove(parentIndex);
			fm.getRenamingsManager().renameFeature(parent.getName(), "A" + parent.getName().substring(1));
			int childrenCount = random.nextInt(maxChildren) + 1;
			childrenCount = Math.min(childrenCount, numberOfFeatures - count);
			for (int i = 1; i <= childrenCount; i++) {
				Feature child = new Feature(fm, "C" + (count + i));
				fm.addFeature(child);
				parent.addChild(child);
				leaves.add(child);
			}
			if (random.nextBoolean()) {
				parent.changeToAnd();
				for (Feature child : parent.getChildren())
					child.setMandatory(random.nextBoolean());
			}
			else if (random.nextBoolean())
				parent.changeToOr();
			count += childrenCount;
		}
		fm.getRenamingsManager().performRenamings();
		return fm;
	}
	
	public static void generateConstraints(FeatureModel fm, Random random, int numberOfConstraints) {
		boolean valid = true;
		try {
			valid = fm.getAnalyser().isValid();
			if (!valid)
				FMCorePlugin.getDefault().logInfo("Feature model not valid!");
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		Object[] names = fm.getRenamingsManager().getOldFeatureNames().toArray();
		int k = 0;
		for (int i = 0; i < numberOfConstraints;) {
			Node node = getRandomLiteral(names, random);
			for (int j = random.nextInt(maxLiterals - minLiterals + 1) + minLiterals; j > 1; j--) {
				if (random.nextBoolean()) {
					if (random.nextBoolean())
						node = new And(node, getRandomLiteral(names, random));
					else
						node = new Or(node, getRandomLiteral(names, random));
				}
				else {
					if (random.nextBoolean())
						node = new Implies(node, getRandomLiteral(names, random));
					else
						node = new Equals(node, getRandomLiteral(names, random));	
				}
				if (random.nextBoolean() && random.nextBoolean())
					node = new Not(node);
			}
			fm.addPropositionalNode(node);
			try {
				if (!valid || fm.getAnalyser().isValid()) {
					i++;
					System.out.println("E\t" + i + "\t" + node);
				}
				else {
					fm.removePropositionalNode(node);
					FMCorePlugin.getDefault().logInfo("F\t" + ++k + "\t" + node);
				}
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
				fm.removePropositionalNode(node);
			}
		}		
	}

	public static FeatureModel refactoring(FeatureModel originalFM, long id, int numberOfEdits) {
		FeatureModel fm = originalFM.clone();
		Random random = new Random(id);
		
		for (int i = 0; i < numberOfEdits; i++) {
			List<Feature> list = new LinkedList<Feature>(fm.getFeatures());
			List<Feature> randomizedList = new LinkedList<Feature>();
			while (!list.isEmpty())
				randomizedList.add(list.remove(random.nextInt(list.size())));
			int r = random.nextInt(3);
			if (r == 0) {
				//Alternative to Or+Constraint
				for (Feature feature : randomizedList)
					if (feature.getChildrenCount() > 1 && feature.isAlternative()) {
						feature.changeToOr();
						LinkedList<Node> nodes = new LinkedList<Node>();
						for (Feature child : feature.getChildren())
							nodes.add(new Literal(child.getName()));
						fm.addPropositionalNode(new AtMost(1,nodes).toCNF());
						break;
					}
			}
			else if (r == 1) {
				//Mandatory to Optional+Constraint
				for (Feature feature : randomizedList) {
					Feature parent = feature.getParent();
					if (parent != null && parent.isAnd() && !parent.isFirstChild(feature) && feature.isMandatory()) {
						feature.setMandatory(false);
						fm.addPropositionalNode(new Implies(new Literal(parent.getName()),new Literal(feature.getName())));
						break;
					}
				}
			}
			else {
				//move feature to parent's parent
				for (Feature child : randomizedList) {
					Feature feature = child.getParent();
					if (feature != null && feature.isMandatory() && feature.isAnd() && !feature.isFirstChild(child)) {
						Feature parent = feature.getParent();
						if (parent != null && parent.isAnd()) {
							feature.removeChild(child);
							parent.addChild(child);
							break;
						}
					}
				}
			}
		}
		return fm;
	}

	public static FeatureModel generalization(FeatureModel originalFM, long id, int numberOfEdits) {
		FeatureModel fm = originalFM.clone();
		Random random = new Random(id);
		
		for (int i = 0; i < numberOfEdits; i++) {
			List<Feature> list = new LinkedList<Feature>(fm.getFeatures());
			List<Feature> randomizedList = new LinkedList<Feature>();
			while (!list.isEmpty())
				randomizedList.add(list.remove(random.nextInt(list.size())));
			int r = 1 + random.nextInt(9);
			if (r == 1) {
				//Alternative to Or
				for (Feature feature : randomizedList)
					if (feature.getChildrenCount() > 1 && feature.isAlternative()) {
						feature.changeToOr();
						break;
					}
			}
			else if (r == 2) {
				//move Optional into Or
				r2:
				for (Feature feature : randomizedList) {
					Feature parent = feature.getParent();
					if (parent != null && parent.isAnd() && feature.isMandatory() && feature.isOr()) {
						for (Feature child : parent.getChildren()) 
							if (!child.isMandatory()) {
								parent.removeChild(child);
								feature.addChild(child);
								break r2;
							}
					}
				}
			}
			else if (r == 3) {
				//And to Or
				for (Feature feature : randomizedList)
					if (feature.getChildrenCount() > 1 && feature.isAnd()) {
						feature.changeToOr();
						break;
					}
			}
			else if (r == 4) {
				//new feature in Alternative
				for (Feature feature : randomizedList)
					if (feature.hasChildren() && feature.isAlternative()) {
						int j = 1;
						Feature child;
						do {
							child = new Feature(fm, "C" + j++);
						} while (!fm.addFeature(child));
						feature.addChild(child);
						break;
					}
			}
			else if (r == 5) {
				//Or to And
				for (Feature feature : randomizedList)
					if (feature.getChildrenCount() > 1 && feature.isOr()) {
						Feature parent = feature.getParent();
						if (parent != null && !parent.isFirstChild(feature) && parent.isAnd()) {
							parent.removeChild(feature);
							for (Feature child : feature.getChildren()) {
								parent.addChild(child);
								child.setMandatory(false);
							}
							break;
						}
					}
			}
			else if (r == 6) {
				//Mandatory to Optional
				for (Feature feature : randomizedList) {
					Feature parent = feature.getParent();
					if (parent != null && parent.isAnd() && !parent.isFirstChild(feature) && feature.isMandatory()) {
						feature.setMandatory(false);
						fm.addPropositionalNode(new Implies(new Literal(parent.getName()),new Literal(feature.getName())));
						break;
					}
				}
			}
			else if (r == 7) {
				//Alternative to And
				for (Feature feature : randomizedList)
					if (feature.getChildrenCount() > 1 && feature.isAlternative()) {
						Feature parent = feature.getParent();
						if (parent != null && !parent.isFirstChild(feature) && parent.isAnd()) {
							parent.removeChild(feature);
							for (Feature child : feature.getChildren()) {
								parent.addChild(child);
								child.setMandatory(false);
							}
							break;
						}
					}
			}
			else if (r == 8) {
				//new Optional in And
				for (Feature feature : randomizedList)
					if (feature.hasChildren() && feature.isAnd()) {
						int j = 1;
						Feature child;
						do {
							child = new Feature(fm, "C" + j++);
						} while (!fm.addFeature(child));
						child.setMandatory(false);
						feature.addChild(child);
						break;
					}
			}
			else {
				//remove Constraint
				List<Node> nodes = fm.getPropositionalNodes();
				if (!nodes.isEmpty()) {
					int index = random.nextInt(nodes.size());
					fm.removePropositionalNode(nodes.get(index));
				}
			}
		}
		return fm;
	}

	public static FeatureModel arbitraryEdits(FeatureModel originalFM, long id, int numberOfEdits) {
		boolean valid = false;
		try {
			valid = originalFM.getAnalyser().isValid();
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		FeatureModel fm = originalFM.clone();
		Random random = new Random(id);
		
		for (int i = 0; i < numberOfEdits; i++) {
			FeatureModel backup = valid ? fm.clone() : null;
			
			List<Feature> list = new LinkedList<Feature>(fm.getFeatures());
			List<Feature> randomizedList = new LinkedList<Feature>();
			while (!list.isEmpty())
				randomizedList.add(list.remove(random.nextInt(list.size())));
			int r = 1 + random.nextInt(5);
			if (r == 1) {
				//delete or add feature
				if (random.nextBoolean())
					for (Feature feature : randomizedList) {
						Feature parent = feature.getParent();
						if (!feature.hasChildren() && parent != null && !parent.isFirstChild(feature)) {
							fm.deleteFeature(feature);
							break;
						}
					}
				else
					for (Feature feature : randomizedList)
						if (feature.hasChildren()) {
							int j = 1;
							Feature child;
							do {
								child = new Feature(fm, "C" + j++);
							} while (!fm.addFeature(child));
							feature.addChild(child);
							break;
						}
			}
			else if (r == 2) {
				//alter group type
				for (Feature feature : randomizedList) {
					if (feature.hasChildren()) {
						if (feature.isAlternative())
							if (random.nextBoolean())
								feature.changeToAnd();
							else
								feature.changeToOr();
						else if (feature.isAnd())
							if (random.nextBoolean())
								feature.changeToAlternative();
							else
								feature.changeToOr();
						else
							if (random.nextBoolean())
								feature.changeToAnd();
							else
								feature.changeToAlternative();
						break;
					}
				}
			}
			else if (r == 3) {
				//change mandatory/optional
				for (Feature feature : randomizedList) {
					Feature parent = feature.getParent();
					if (parent != null && parent.isAnd() && !parent.isFirstChild(feature)) {
						feature.setMandatory(!feature.isMandatory());
						break;
					}
				}
			}
			else if (r == 4) {
				//move a concrete feature to another branch
				for (Feature feature : randomizedList) {
					Feature parent = feature.getParent();
					if (!feature.hasChildren() && parent != null && !parent.isFirstChild(feature)) {
						parent.removeChild(feature);
						Feature newParent = parent;
						for (Feature compound : randomizedList)
							if (compound != parent && compound.hasChildren())
								newParent = compound;
						newParent.addChild(feature);
						break;
					}
				}
			}
			else {
				//delete or add constraint
				if (fm.getPropositionalNodes().size() > 0 && random.nextBoolean()) {
					int index = random.nextInt(fm.getPropositionalNodes().size());
					fm.removeConstraint(index);
				}
				else
					generateConstraints(fm, random, 1);
			}
			
			try {
				if (valid && !fm.getAnalyser().isValid()) {
					System.out.println("Void feature model by arbitrary edit	" + r);
					fm = backup;
					i--;
				}
			} catch (TimeoutException e) {
				FMCorePlugin.getDefault().logError(e);
			}
		}
		return fm;
	}

	private static Literal getRandomLiteral(Object[] names, Random random) {
		int index = random.nextInt(names.length);
		return new Literal(names[index], random.nextBoolean());
	}
	
	public static String getTimeString(long dur) {
		if (dur < 1000000)
			return dur + "nsec";
		dur /= 1000000;
		if (dur < 1000)
			return dur + "msec";
		dur /= 1000;
		if (dur < 60)
			return dur + "sec";
		dur /= 60;
		if (dur < 60)
			return dur + "min";
		dur /= 60;
		return dur + "h";
	}

}
