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
package de.ovgu.featureide.fm.core;

import java.awt.Point;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.QualifiedName;
import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * The model representation of the feature tree that notifies listeners of
 * changes in the tree.
 * 
 * @author Thomas Thuem
 * 
 */
public class FeatureModel implements PropertyConstants {

	public static final String COMPOSER_KEY = "composer";
	public static final QualifiedName composerConfigID = new QualifiedName("featureproject.configs", "composer");
	public static final QualifiedName sourceFolderConfigID = new QualifiedName("featureproject.configs", "source");
	public static final String SOURCE_ARGUMENT = "source";
	public static final String DEFAULT_SOURCE_PATH = "src";
	public static final String BUILDER_ID = "de.ovgu.featureide.core" + ".extensibleFeatureProjectBuilder";
	
	/**
	 * the root feature
	 */
	private Feature root;
	private boolean legend=false;

	private Point legendPos= new Point(0,0);
	/**
	 * a hashtable containing all features
	 */
	private Hashtable<String, Feature> featureTable = new Hashtable<String, Feature>();

	/**
	 * all comment lines from the model file without line number at which they
	 * occur
	 */

	private List<String> comments = new LinkedList<String>();

	/**
	 * 
	 */
	private List<Node> propNodes = new LinkedList<Node>();

	private List<Constraint> constraints = new LinkedList<Constraint>();

	/**
	 * This string saves the annotations from the model file as they were read,
	 * because they were not yet used.
	 */
	private List<String> annotations = new LinkedList<String>();

	/**
	 * a list containing all renamings since the last save
	 */
	private LinkedList<Renaming> renamings = new LinkedList<Renaming>();

	private IFolder sourceFolder;
	
	private IFMComposerExtension fmComposerExtension = new FMComposerExtension();
	private String COMPOSER_ID;

	/**
	 * @return the fMComposerExtension
	 */
	public IFMComposerExtension getFMComposerExtension(IProject project) {
		setComposerID(project);
		setComposer();
		return fmComposerExtension;
	}

	public FeatureModel() {
		reset();
	}

	public void reset() {
		if (root != null) {
			while (root.hasChildren()) {
				Feature child = root.getLastChild();
				deleteChildFeatures(child);
				root.removeChild(child);
				featureTable.remove(child);
			}
			root = null;
		}
		featureTable.clear();
		renamings.clear();
		propNodes.clear();
		constraints.clear();
		comments.clear();
		annotations.clear();
	}

	private void deleteChildFeatures(Feature feature) {
		while (feature.hasChildren()) {
			Feature child = feature.getLastChild();
			deleteChildFeatures(child);
			feature.removeChild(child);
			featureTable.remove(child);
		}
	}

	public List<String> getAnnotations() {
		return Collections.unmodifiableList(annotations);
	}

	public void addAnnotation(String annotation) {
		annotations.add(annotation);
	}

	public List<String> getComments() {
		return Collections.unmodifiableList(comments);
	}

	public void addComment(String comment) {
		comments.add(comment);
	}

	public List<Node> getPropositionalNodes() {
		return Collections.unmodifiableList(propNodes);
	}

	public void addPropositionalNode(Node node) {
		propNodes.add(node);
		constraints.add(new Constraint(this, node));
	}

	public void removePropositionalNode(Node node) {
		propNodes.remove(node);
		constraints.remove(constraints.size() - 1);
	}

	public void removePropositionalNode(Constraint constraint) {

		propNodes.remove(constraint.getNode());
		constraints.remove(constraint);

	}

	public void removePropositionalNode(int index) {
		propNodes.remove(index);
		constraints.remove(constraints.size() - 1);
	}

	public Feature getRoot() {
		return root;
	}

	public void setRoot(Feature root) {
		this.root = root;
	}

	public boolean addFeature(Feature feature) {
		String name = feature.getName();
		if (featureTable.containsKey(name))
			return false;
		featureTable.put(name, feature);
		return true;
	}

	public void deleteFeatureFromTable(Feature feature) {
		featureTable.remove(feature.getName());
	}

	public boolean deleteFeature(Feature feature) {
		// the root can not be deleted
		if (feature == root)
			return false;

		// check if it exists
		String name = feature.getName();
		if (!featureTable.containsKey(name))
			return false;
		
		// use the group type of the feature to delete
		Feature parent = feature.getParent();
		if (parent.getChildrenCount() == 1) {
			if (feature.isAnd())
				parent.setAnd();
			else if (feature.isAlternative())
				parent.setAlternative();
			else
				parent.setOr();
		}

		// add children to parent
		int index = parent.getChildIndex(feature);
		while (feature.hasChildren())
			parent.addChildAtPosition(index, feature.removeLastChild());

		// delete feature
		parent.removeChild(feature);
		featureTable.remove(name);
		return true;
	}

	public Feature getFeature(String name) {
		if (featureTable.isEmpty()) {
			// create the root feature (it is the only one without a reference)
			root = new Feature(this, name);
			addFeature(root);
			return root;
		}
		return featureTable.get(name);
	}

	public boolean renameFeature(String oldName, String newName) {
		if (!featureTable.containsKey(oldName)
				|| featureTable.containsKey(newName))
			return false;
		Feature feature = featureTable.remove(oldName);
		feature.setName(newName);
		featureTable.put(newName, feature);
		renamings.add(new Renaming(oldName, newName));
		for (Node node : propNodes) {
			renameVariables(node, oldName, newName);
		}
		return true;
	}

	public boolean isRenamed() {
		return (renamings.size() != 0);
	}

	public void performRenamings() {
		for (Renaming renaming : renamings) {
			for (Node node : propNodes)
				renameVariables(node, renaming.oldName, renaming.newName);
		}
		renamings.clear();
	};

	public void performRenamings(IFile file) {
		IProject project = ((IResource) file.getAdapter(IFile.class)).getProject();
		String sourceName = getProjectConfigurationPath(project);
		if (sourceName != null && !sourceName.equals("")) {
			sourceFolder = project.getFolder(sourceName);
		}
		for (Renaming renaming : renamings) {
			if (!performComposerRenamings(renaming.oldName, renaming.newName,
				project)) {
				moveFolder(renaming.oldName, renaming.newName);
			}
		}
		renamings.clear();
	}
	
	private boolean performComposerRenamings(final String oldName,
			final String newName, final IProject project) {
		return getFMComposerExtension(project).performRenaming(oldName,newName, project);
	}

	public void moveFolder(String oldName, String newName) {
		try {
			IFolder folder = sourceFolder.getFolder(oldName);
			if (folder.exists()) {
				if (!sourceFolder.getFolder(newName).exists()) {
					IPath newPath = sourceFolder.getFolder(newName)
							.getFullPath();
					folder.move(newPath, true, null);
				} else {
					move(folder, oldName, newName);
				}
			}
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * @param folder
	 * @param oldName
	 * @param newName
	 * @throws CoreException
	 */
	private void move(IFolder folder, String oldName, String newName)
			throws CoreException {
		for (IResource res : folder.members()) {
			if (res instanceof IFile) {
				IFile newfile = sourceFolder.getFolder(newName).getFile(
						res.getName());
				if (!newfile.exists()) {
					res.move(newfile.getRawLocation(), true, null);
				}
			}
			if (res instanceof IFolder) {
				IFolder newfile = sourceFolder.getFolder(newName).getFolder(
						res.getName());
				if (!newfile.exists()) {
					res.move(newfile.getRawLocation(), true, null);
				}
			}
		}
	}

	private void renameVariables(Node node, String oldName, String newName) {
		if (node instanceof Literal) {
			if (oldName.equals(((Literal) node).var))
				((Literal) node).var = newName;
			return;
		}

		for (Node child : node.getChildren())
			renameVariables(child, oldName, newName);
	}

	public boolean containsLayer(String featureName) {
		Feature feature = featureTable.get(featureName);
		return feature != null && feature.isLayer();
	}

	private final LinkedList<PropertyChangeListener> listenerList = new LinkedList<PropertyChangeListener>();

	public void addListener(PropertyChangeListener listener) {
		if (!listenerList.contains(listener))
			listenerList.add(listener);
	}

	public void removeListener(PropertyChangeListener listener) {
		listenerList.remove(listener);
	}

	public void handleModelDataLoaded() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				MODEL_DATA_LOADED, false, true);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	public void handleModelDataChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				MODEL_DATA_CHANGED, false, true);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	public void redrawDiagram() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				REDRAW_DIAGRAM, false, true);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	public Collection<Feature> getFeatures() {
		return Collections.unmodifiableCollection(featureTable.values());
	}

	/*
	 * public Collection<Feature> getLayers() { LinkedList<Feature> layers = new
	 * LinkedList<Feature>(); for (Feature feature : featureTable.values()) if
	 * (feature.isConcrete()) layers.add(feature); return
	 * Collections.unmodifiableCollection(layers); }
	 */
	private LinkedList<Feature> layers = new LinkedList<Feature>();

	public Collection<Feature> getLayers() {
		layers.clear();
		if (root != null) {
			initFeatures(root);
		}
		return Collections.unmodifiableCollection(layers);
	}

	private void initFeatures(Feature feature) {
		if (feature.isConcrete())
			layers.add(feature);
		for (Feature child : feature.getChildren())
			initFeatures(child);
	}

	public Collection<String> getLayerNames() {
		ArrayList<String> layerNames = new ArrayList<String>();
		if (root == null)
			return null;
		for (Feature layer : getLayers()) {
			layerNames.add(layer.getName());
		}
		return layerNames;
	}

	public void createDefaultValues() {
		Feature root = getFeature("Root");
		root.setAbstract(true);
		Feature feature = new Feature(this, "Base");
		root.addChild(feature);
		addFeature(feature);
	}

	public void replaceRoot(Feature feature) {
		featureTable.remove(root.getName());
		root = feature;
	}

	/**
	 * Returns the current name of a feature given its name at the last save.
	 * 
	 * @param name
	 *            name when last saved
	 * @return current name of this feature
	 */
	public String getNewName(String name) {
		for (Renaming renaming : renamings)
			if (renaming.oldName.equals(name))
				name = renaming.newName;
		return name;
	}

	/**
	 * Returns the name of a feature at the time of the last save given its
	 * current name.
	 * 
	 * @param name
	 *            current name of a feature
	 * @return name when last saved
	 */
	public String getOldName(String name) {
		for (int i = renamings.size() - 1; i >= 0; i--)
			if (renamings.get(i).newName.equals(name))
				name = renamings.get(i).oldName;
		return name;
	}

	public Set<String> getFeatureNames() {
		return Collections.unmodifiableSet(featureTable.keySet());
	}

	public Set<String> getOldFeatureNames() {
		Set<String> names = new HashSet<String>(featureTable.keySet());
		for (int i = renamings.size() - 1; i >= 0; i--) {
			Renaming renaming = renamings.get(i);
			names.remove(renaming.newName);
			names.add(renaming.oldName);
		}
		return Collections.unmodifiableSet(names);
	}

	public Node getConstraint(int index) {
		return propNodes.get(index);
	}

	public int getConstraintCount() {
		return constraints.size();
	}

	public List<Constraint> getConstraints() {
		return Collections.unmodifiableList(constraints);
	}
	
	public void replacePropNode(int index, Node node){
		assert(index<constraints.size());
		constraints.set(index, new Constraint(this, node));
		propNodes.set(index, node);
		
	}
	
	
	public int getNumberOfFeatures() {
		return featureTable.size();
	}

	@Override
	public FeatureModel clone() {
		FeatureModel fm = new FeatureModel();
		fm.root = root.clone();
		List<Feature> list = new LinkedList<Feature>();
		list.add(fm.root);
		while (!list.isEmpty()) {
			Feature feature = list.remove(0);
			fm.featureTable.put(feature.getName(), feature);
			for (Feature child : feature.getChildren())
				list.add(child);
		}
		fm.propNodes = new LinkedList<Node>();
		for (Node node : propNodes) {
			fm.propNodes.add(node);

			fm.constraints.add(new Constraint(fm, node));
		}
		for (int i = 0; i < annotations.size(); i++)
			fm.annotations.add(annotations.get(i));
		for (int i = 0; i < comments.size(); i++)
			fm.comments.add(comments.get(i));
		return fm;
	}

	public boolean isValid() throws TimeoutException {
		Node root = NodeCreator.createNodes(this);
		return new SatSolver(root, 1000).isSatisfiable();
	}

	/**
	 * checks whether A implies B for the current feature model.
	 * 
	 * in detail the following condition should be checked whether
	 * 
	 * FM => ((A1 and A2 and ... and An) => (B1 and B2 and ... and Bn))
	 * 
	 * is true for all values
	 * 
	 * @param A
	 *            set of features that form a conjunction
	 * @param B
	 *            set of features that form a conjunction
	 * @return
	 * @throws TimeoutException
	 */
	public boolean checkImplies(Set<Feature> a, Set<Feature> b)
			throws TimeoutException {
		if (b.isEmpty())
			return true;

		Node featureModel = NodeCreator.createNodes(this);

		// B1 and B2 and ... Bn
		Node condition = conjunct(b);
		// (A1 and ... An) => (B1 and ... Bn)
		if (!a.isEmpty())
			condition = new Implies(conjunct(a), condition);
		// FM => (A => B)
		Implies finalFormula = new Implies(featureModel, condition);
		return !new SatSolver(new Not(finalFormula), 1000).isSatisfiable();
	}

	/**
	 * checks some condition against the feature model. use only if you know
	 * what you are doing!
	 * 
	 * @return
	 * @throws TimeoutException
	 */
	public boolean checkCondition(Node condition) {

		Node featureModel = NodeCreator.createNodes(this);
		// FM => (condition)
		Implies finalFormula = new Implies(featureModel, condition.clone());
		try {
			return !new SatSolver(new Not(finalFormula), 1000).isSatisfiable();
		} catch (TimeoutException e) {
			FMCorePlugin.getDefault().logError(e);
			return false;
		}
	}

	/**
	 * Checks whether the given featureSets are mutually exclusive in the given
	 * context and for the current feature model.
	 * 
	 * In detail it is checked whether FM => (context => (at most one of the
	 * featureSets are present)) is a tautology.
	 * 
	 * Here is an example for a truth table of
	 * "at most one the featureSets are present" for three feature sets A, B and
	 * C:
	 * 
	 * A B C result ------------------------ T T T F T T F F T F T F T F F T F T
	 * T F F T F T F F T T F F F T
	 * 
	 * If you want to check XOR(featureSet_1, ..., featureSet_n) you can call
	 * areMutualExclusive() && !mayBeMissing().
	 * 
	 * @param context
	 *            context in which everything is checked
	 * @param featureSets
	 *            list of feature sets that are checked to be mutually exclusive
	 *            in the given context and for the current feature model
	 * 
	 * @return true, if the feature sets are mutually exclusive || false,
	 *         otherwise
	 * @throws TimeoutException
	 */
	public boolean areMutualExclusive(Set<Feature> context,
			List<Set<Feature>> featureSets) throws TimeoutException {
		if ((featureSets == null) || (featureSets.size() < 2))
			return true;

		Node featureModel = NodeCreator.createNodes(this);

		ArrayList<Node> conjunctions = new ArrayList<Node>(featureSets.size());
		for (Set<Feature> features : featureSets) {
			if ((features != null) && !features.isEmpty())
				conjunctions.add(conjunct(features));
			else
				// If one feature set is empty (i.e. the code-fragment is always
				// present) than it cannot be
				// mutually exclusive to the other ones.
				return false;
		}

		// We build the conjunctive normal form of the formula to check
		LinkedList<Object> forOr = new LinkedList<Object>();
		LinkedList<Object> allNot = new LinkedList<Object>();
		for (int i = 0; i < conjunctions.size(); ++i) {
			allNot.add(new Not(conjunctions.get(i).clone()));

			LinkedList<Object> forAnd = new LinkedList<Object>();
			for (int j = 0; j < conjunctions.size(); ++j) {
				if (j == i)
					forAnd.add(conjunctions.get(j).clone());
				else
					forAnd.add(new Not(conjunctions.get(j).clone()));
			}
			forOr.add(new And(forAnd));
		}
		forOr.add(new And(allNot));

		Node condition = new Or(forOr);
		if ((context != null) && !context.isEmpty())
			condition = new Implies(conjunct(context), condition);

		Implies finalFormula = new Implies(featureModel, condition);
		return !new SatSolver(new Not(finalFormula), 1000).isSatisfiable();
	}

	/**
	 * Checks whether there exists a set of features that is valid within the
	 * feature model and the given context, so that none of the given feature
	 * sets are present, i.e. evaluate to true.
	 * 
	 * In detail it is checked whether there exists a set F of features so that
	 * eval(FM, F) AND eval(context, F) AND NOT(eval(featureSet_1, F)) AND ...
	 * AND NOT(eval(featureSet_n, F)) is true.
	 * 
	 * If you want to check XOR(featureSet_1, ..., featureSet_n) you can call
	 * areMutualExclusive() && !mayBeMissing().
	 * 
	 * @param context
	 *            context in which everything is checked
	 * @param featureSets
	 *            list of feature sets
	 * 
	 * @return true, if there exists such a set of features, i.e. if the
	 *         code-fragment may be missing || false, otherwise
	 * @throws TimeoutException
	 */
	public boolean mayBeMissing(Set<Feature> context,
			List<Set<Feature>> featureSets) throws TimeoutException {
		if ((featureSets == null) || featureSets.isEmpty())
			return false;

		Node featureModel = NodeCreator.createNodes(this);
		LinkedList<Object> forAnd = new LinkedList<Object>();

		for (Set<Feature> features : featureSets) {
			if ((features != null) && !features.isEmpty())
				forAnd.add(new Not(conjunct(features)));
			else
				return false;
		}

		Node condition = new And(forAnd);
		if ((context != null) && !context.isEmpty())
			condition = new And(conjunct(context), condition);

		Node finalFormula = new And(featureModel, condition);
		return new SatSolver(finalFormula, 1000).isSatisfiable();
	}

	/**
	 * Checks whether there exists a set of features that is valid within the
	 * feature model, so that all given features are present.
	 * 
	 * In detail it is checked whether there exists a set F of features so that
	 * eval(FM, F) AND eval(feature_1, F) AND eval(feature_n, F) is true.
	 * 
	 * @param features
	 * 
	 * @return true if there exists such a set of features || false, otherwise
	 * @throws TimeoutException
	 */
	public boolean exists(Set<Feature> features) throws TimeoutException {
		if ((features == null) || (features.isEmpty()))
			return true;

		Node featureModel = NodeCreator.createNodes(this);
		Node finalFormula = new And(featureModel, conjunct(features));
		return new SatSolver(finalFormula, 1000).isSatisfiable();
	}

	private Node conjunct(Set<Feature> b) {
		Iterator<Feature> iterator = b.iterator();
		Node result = new Literal(
				NodeCreator.getVariable(iterator.next(), this));
		while (iterator.hasNext())
			result = new And(result, new Literal(NodeCreator.getVariable(
					iterator.next(), this)));

		return result;
	}

	public int countConcreteFeatures() {
		int number = 0;
		for (Feature feature : getFeatures())
			if (feature.isConcrete())
				number++;
		return number;
	}

	public int countTerminalFeatures() {
		int number = 0;
		for (Feature feature : getFeatures())
			if (!feature.hasChildren())
				number++;
		return number;
	}

	/**
	 * Returns the list of features that occur in all variants, where one of the
	 * given features is selected. If the given list of features is empty, this
	 * method will calculate the features that are present in all variants
	 * specified by the feature model.
	 * 
	 * @param timeout
	 *            in milliseconds
	 * @param selectedFeatures
	 *            a list of feature names for which
	 * @return a list of features that is common to all variants
	 */
	public Collection<String> commonFeatures(long timeout,
			Object... selectedFeatures) {
		Node formula = NodeCreator.createNodes(this);
		if (selectedFeatures.length > 0)
			formula = new And(formula, new Or(selectedFeatures));
		SatSolver solver = new SatSolver(formula, timeout);
		List<String> common = new LinkedList<String>();
		for (Literal literal : solver.knownValues())
			if (literal.positive)
				common.add(literal.var.toString());
		return common;
	}

	public List<Literal> getDeadFeatures() {
		Node root = NodeCreator.createNodes(this);
		List<Literal> set = new ArrayList<Literal>();
		for (Literal e : new SatSolver(root, 1000).knownValues()) {
			if (!e.positive) {
				set.add(e);
			}
		}
		return set;

	}

	/**
	 * Checks a string to be a valid featurename.
	 * 
	 * @param s  Possible featurename to be checked
	 * @return boolean
	 */
	public static boolean isValidJavaIdentifier(String s) {
		if (s == null)
			return false;
		final int len = s.length();
		if (len == 0 || !Character.isJavaIdentifierStart(s.charAt(0)))
			return false;
		for (int i = 1; i < len; i++) {
			if (!Character.isJavaIdentifierPart(s.charAt(i)))
				return false;
		}
		return true;
	}

	public String getProjectConfigurationPath(IProject project) {
		try {
			String path = project.getPersistentProperty(sourceFolderConfigID);
			if (path != null)
				return path;

			path = getPath(project, SOURCE_ARGUMENT);
			if (path == null)
				return DEFAULT_SOURCE_PATH;
			return path;
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return DEFAULT_SOURCE_PATH;
	}

	private String getPath(IProject project, String argument) {
		try {
			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (command.getBuilderName().equals(BUILDER_ID)) {
					String path = (String) command.getArguments().get(argument);
					return path;
				}
			}
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return null;
	}

	private void setComposerID(IProject project) {
		try {
			String id = project.getPersistentProperty(composerConfigID);
			if (id != null) {
				COMPOSER_ID = id;
				return;
			}

			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (command.getBuilderName().equals(BUILDER_ID)) {
					id = (String) command.getArguments().get(COMPOSER_KEY);
					if (id != null) {
						COMPOSER_ID = id;
						return;
					}
				}
			}

		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		COMPOSER_ID = null;
	}
	
	private void setComposer() {
		if (COMPOSER_ID == null) {
			return;
		}
		
		IConfigurationElement[] config = Platform.getExtensionRegistry()
				.getConfigurationElementsFor(FMCorePlugin.PLUGIN_ID + ".FMComposer");
		try {
			for (IConfigurationElement e : config) {
				if (e.getAttribute("composer").equals(COMPOSER_ID)) {
					final Object o = e.createExecutableExtension("class");
					if (o instanceof IFMComposerExtension) {
						fmComposerExtension = (IFMComposerExtension)o;
					}
				}
			}
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	/**
	 * @return
	 */
	public boolean hasLegend() {
		// TODO Auto-generated method stub
		return this.legend;
	}

	public void setLegend(boolean b) {
		// TODO Auto-generated method stub
		this.legend = b;
	}


	public Point getLegendPos() {
		
		return legendPos;
	}
	public void setLegendPos(int x, int y){
		this.legendPos = new Point(x,y);
	}
}