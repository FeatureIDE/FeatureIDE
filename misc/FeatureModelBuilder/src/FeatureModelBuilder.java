
import java.util.ArrayList;
import java.util.LinkedList;

import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Not;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;

/**
 * Generates all valid feature models for a given number of concrete features.
 * @author Jens Meinicke
 *
 */
public class FeatureModelBuilder {

	/**
	 * The maximal length of sorted models.<br>
	 * The index equals the hash value of the model modulo this value.<br>
	 * This value is proportional to the required memory.
	 */
	private static final int MODULO = 100000;

	private static final boolean COUNT_INVALID_MODELS = false;
	
	/**
	 * The number of features inclusive the root.
	 */
	private static int COUNT_FEATURES = 5;
	
	/**
	 * The index equals the number of features of the models at this position.<br>
	 * Does only contain models without cross-tree constraints
	 */
	private LinkedList<LinkedList<FeatureModel>> models = new LinkedList<LinkedList<FeatureModel>>();

	/**
	 * first index: The models with an equivalent hash value modulo the selected modulo value<br>
	 * second index: Differing models
	 */
	private ArrayList<LinkedList<FeatureModelCounter>> sortedModels = new ArrayList<LinkedList<FeatureModelCounter>>(MODULO);
	
	public ArrayList<LinkedList<FeatureModelCounter>> getSortedModels() {
		return sortedModels;
	}

	public static void main(String[] args) {
		long time = System.currentTimeMillis();	
		final FeatureModelBuilder builder = new FeatureModelBuilder(COUNT_FEATURES);
		for (int i = 0;i <= COUNT_FEATURES;i++) {
			builder.getModels(i);
			builder.renameAllModels(i);
		}
		try {
			/* generating in multiple threads is to memory intensive */
			builder.createConstraints(COUNT_FEATURES);
		} catch (TimeoutException e1) {
			e1.printStackTrace();
		}
		time = System.currentTimeMillis() - time;
		System.out.println("Calculation for " + (COUNT_FEATURES-1) + " features finished("+time+" ms)");

		for (int n = 2;n <= 6;n++) {
			Double number = (double) (n==2 ? 2 : 
						  n==3 ? 10 :
						  n==4 ? 218 :
						  n==5 ? 64594 :
						  n==6 ? 42946420349.0 :	  
						  -1);
			if (COUNT_INVALID_MODELS) {
				number = Math.pow(2, Math.pow(2, n-1));
			}
			Double counter = (double) 0;
			if (n == COUNT_FEATURES) {
				for (LinkedList<FeatureModelCounter> list : builder.getSortedModels()) {
					counter += list.size();
				}
			} else {
				if (!COUNT_INVALID_MODELS) {
					counter = (double) (n==2 ? 2 :
						  n==3 ? 10 :
						  n==4 ? 112 :
						  n==5 ? 2570 :
						  n==6 ? 113544 :
						  -1);
				} else {
					counter = (double) (n==2 ? 4 :
						  n==3 ? 16 :
						  n==4 ? 150 :
						  -1);
				}
			}
			Double percentage = (counter / number)*100;
			System.out.println();
			System.out.print("Feature " + (n-1) + " -> #Models " + counter + "/" + number + " = " + percentage + "%");
			if (n == COUNT_FEATURES) {
				System.out.print(" RECALCULATED");
			}
		}
	}

	public FeatureModelBuilder(int countFeaturesMax) {
		for (int j  = 0;j <= countFeaturesMax; j++) {
			models.add(new LinkedList<FeatureModel>());
		}
		FeatureModel model = new FeatureModel();
		model.setRoot(new Feature(model, ""));
		models.get(1).add(model);
	}

	/**
	 * Creates all possible models without constraints.
	 * @param countFeatures
	 * @return
	 */
	private LinkedList<FeatureModel> getModels(int countFeatures) {
		if (!models.get(countFeatures).isEmpty()) {
			return models.get(countFeatures);
		}
		
		// case: root is ALTERNATIVE
		FeatureModel model = new FeatureModel();
		model.setRoot(new Feature(model, ""));
		model.getRoot().setAlternative();
		LinkedList<FeatureModel> newModels = addChildren(countFeatures - 1, model);
		models.get(countFeatures).addAll(newModels);
		
		// case: root is OR
		model = new FeatureModel();
		model.setRoot(new Feature(model, ""));
		model.getRoot().setOr();	
		newModels = addChildren(countFeatures - 1, model);
		models.get(countFeatures).addAll(newModels);
		
		// case: root is AND
		model = new FeatureModel();
		model.setRoot(new Feature(model, ""));
		model.getRoot().setAnd();
		newModels = addChildren(countFeatures - 1, model);
		models.get(countFeatures).addAll(newModels);

		return models.get(countFeatures);
	}
	
	private LinkedList<FeatureModel> addChildren(int countFeatures, FeatureModel model) {
		LinkedList<FeatureModel> newModels = new LinkedList<FeatureModel>();
		if (countFeatures == 0) {
			newModels.add(model);
			return newModels;
		}
		for (int j = 1;j <= countFeatures; j++) {
			for (FeatureModel m : getModels(j)) {
				Feature root = m.getRoot();
				if (model.getRoot().isAnd()) {
					// case: new child is mandatory
					FeatureModel clone = model.clone();
					Feature child = root.clone();
					child.setMandatory(false);
					clone.getRoot().addChild(child);
					newModels.addAll(addChildren(countFeatures - j, clone));
					
					// case: new child is optional
					clone = model.clone();
					child = root.clone();
					child.setMandatory(true);
					clone.getRoot().addChild(child);
					newModels.addAll(addChildren(countFeatures - j, clone));
				} else if (model.getRoot().hasChildren() || countFeatures - j != 0) {
					FeatureModel clone = model.clone();
					clone.getRoot().addChild(root.clone());
					newModels.addAll(addChildren(countFeatures - j, clone));
				}
			}
		}
		return newModels;
	}
	
	/**
	 * Sets the feature names of all generated Models without constraints to F0,F1,F2...
	 * @param i
	 */
	private void renameAllModels(int i) {
		for (FeatureModel m : models.get(i)) {
			name  = 0;
			Feature root = m.getRoot();
			rename(root);
			initTable(root, m);
		}
	}
	
	private int name = 0;
	private void rename(Feature feature) {
		feature.setName("F" + name++);
		if (!feature.hasChildren()) {
			return;
		}
		
		for (Feature child : feature.getChildren()) {
			if (child.hasChildren()) {
				rename(child);
			} else {
				child.setName("F" + name++);
			}
		}
	}
	
	private void initTable(Feature feature, FeatureModel m) {
		m.addFeature(feature);
		for (Feature child : feature.getChildren()) {
			initTable(child, m);
		}
	}
	

	private int counter = 0;
	
	/**
	 * Adds constraints to all generated models.
	 */
	private void createConstraints(int i) throws TimeoutException {
		while (true) {
			FeatureModel mc = getModel(i);
			if (mc == null) {
				return;
			}
			final LinkedList<FeatureModel> newModelsWithConstraints = new LinkedList<FeatureModel>();
			newModelsWithConstraints.add(mc);
			int output = 1000;
			System.out.println("Generate models for: "+print(mc));
			for (int j  = 0;j < i;j++) {
				System.out.print('*');
				for (int k = 0; k < i; k++) {
					System.out.print('.');
					if (k != j) {
						LinkedList<FeatureModel> newModelsWithConstraints2 = new LinkedList<FeatureModel>();
						for (FeatureModel m : newModelsWithConstraints) {
							// case: A ==> B
							FeatureModel model = m .clone();
							model.addConstraint(new Constraint(model, new Implies(new Literal("F" + j),new Literal("F"+ k))));				
							FeatureModelAnalyzer analyser = model.getAnalyser();
							
							output++;
							if (output>1000) {
								output = 0;
								System.out.print('!');
							}
							if (!COUNT_INVALID_MODELS) {
								if (analyser.isValid() &&
										analyser.getDeadFeatures(1000000).isEmpty() &&
										!isRedundant(m, model)) {
									newModelsWithConstraints2.add(model);
								}
							} else {
								if (!isRedundant(model, m)) {
									newModelsWithConstraints2.add(model);
								}
							}
							if (j > k) {
								// Avoid duplicate Models
								continue;
							}
							
							output++;
							if (output>1000) {
								output = 0;
								System.out.print('!');
							}
							
							// case: A ==> !B
							model = m.clone();
							analyser = model.getAnalyser();
							model.addConstraint(new Constraint(model, new Implies(new Literal("F" + j),new Not(new Literal("F"+ k)))));
							if (!COUNT_INVALID_MODELS) {
								if (analyser.isValid() &&
										analyser.getDeadFeatures(1000000).isEmpty() &&
										!isRedundant(m, model)) {
									newModelsWithConstraints2.add(model);
								}
							} else {
								if (!isRedundant(model, m)) {
									newModelsWithConstraints2.add(model);
								}
							}
						}
						newModelsWithConstraints.addAll(newModelsWithConstraints2);
					}
				}
			}
			
			if (configurations.isEmpty()) {
				initConfigurations(newModelsWithConstraints.getFirst(), i);
			}
			System.out.println();
			System.out.print("Convert to hash (" + newModelsWithConstraints.size() + ") ");
			output = 1000;
			LinkedList<FeatureModelCounter> counterModels = new LinkedList<FeatureModelCounter>(); 
			for (FeatureModel m : newModelsWithConstraints) {
				output++;
				if (output > 1000) {
					output = 0;
					System.out.print('.');
				}
				Double hashCode = hashCode(m);
				FeatureModelCounter c = new FeatureModelCounter(hashCode);
				boolean found = false;
				for (FeatureModelCounter fmc : counterModels) {
					if (fmc.equals(c)) {
						found = true;
					}
				}
				if (!found) {
					counterModels.add(c);
				}
			}
			newModelsWithConstraints.clear();
			System.out.println();
			insert(counterModels);
			System.out.println("Features: " + i + " " + counter++ + "/" + models.get(i).size());	
		}
	}
	
	private boolean isRedundant(FeatureModel fm, FeatureModel dirtyModel) {
		ModelComparator comparator = new ModelComparator(10000);
		Comparison comparison = comparator.compare(fm, dirtyModel);
		if (comparison == Comparison.REFACTORING) {
			return true;
		}
		return false;
	}

	/**
	 * Insets all calculated models into sortedModels.
	 */
	private void insert(LinkedList<FeatureModelCounter> newModelsWithConstraints) {
		
		System.out.print("insert "+ newModelsWithConstraints.size() + " ");
		int output = 0;
		for (FeatureModelCounter newModel : newModelsWithConstraints) {
			int number = (int) (newModel.hashCode%MODULO);
			if (number < 0) {
				number = number*-1;
			}
			while (sortedModels.size() <= number) {
				sortedModels.add(new LinkedList<FeatureModelCounter>());
			}
			if (sortedModels.get(number).isEmpty()) {
				sortedModels.get(number).add(newModel);
			} else {
				boolean found = false;
				for (FeatureModelCounter hash : sortedModels.get(number)) {
					if (hash.equals(newModel.hashCode)) {
						found = true;
						break;
					}
				}
				if (!found) {
					sortedModels.get(number).add(newModel);
				}
			}
			if ((output++)%1000 == 0) {
				System.out.print('.');
			}
		}
		System.out.println();
	}
	
	private LinkedList<Configuration> configurations = new LinkedList<Configuration>();
	
	/**
	 * Generate a hash value for the given model.
	 */
	private Double hashCode(FeatureModel newModel) {
		Double hashCode = 0.0;
		Double multiplier = 1.0;
		for (Configuration conf : configurations) {
			if (new Configuration(conf, newModel).valid()) {
				hashCode += multiplier;
			}
			multiplier = multiplier*2;
		}
		return hashCode;
	}
	
	/**
	 * Initializes configurations for calculation of the hash values.
	 */
	public void initConfigurations(FeatureModel model, int i) {
		Configuration c = new Configuration(model, false, false);
		c.setManual(model.getRoot().getName(), Selection.SELECTED);
		configurations.add(c);
		for (String feature : model.getFeatureNames()) {
			if (feature.equals("") || feature.equals(model.getRoot().getName())) {
				continue;
			}
			LinkedList<Configuration> toAdd = new LinkedList<Configuration>();
			for (Configuration conf : configurations) {
				Configuration configuration = new Configuration(conf);
				configuration.setManual(feature, Selection.SELECTED);
				toAdd.add(configuration);
			}
			configurations.addAll(toAdd);
		}
	}
	
	private FeatureModel getModel(int i) {
		if (models.get(i).isEmpty()) {
			return null;
		}
		return models.get(i).removeLast();		
	}
	
	private String print(FeatureModel fm) {
		String x = printFeatures(fm.getRoot());
		for (Constraint c : fm.getConstraints()) {
			x +=c.toString() + " ";
		}
		return x;
	}

	private String printFeatures(Feature feature) {
		String x = feature.getName();
		if (!feature.hasChildren()) {
			return x;
		}
		if (feature.isOr()) {
			x += " or [";
		} else if (feature.isAlternative()) {
			x += " alt [";
		} else {
			x += " and [";
		}
		
		for (Feature child : feature.getChildren()) {
			x += " ";
			if (feature.isAnd()) {
				if (child.isMandatory()) {
					x += "M ";
				} else {
					x += "O ";
				}
			}
			
			if (child.hasChildren()) {
				x += printFeatures(child);
			} else {
				x += child.getName();
			}
		}
		return x + " ] ";
	}

}
