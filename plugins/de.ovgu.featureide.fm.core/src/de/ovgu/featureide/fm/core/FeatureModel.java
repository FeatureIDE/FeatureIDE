/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import javax.annotation.CheckForNull;
import javax.annotation.Nonnull;

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
import org.prop4j.Literal;
import org.prop4j.Node;
import org.sat4j.specs.TimeoutException;

/**
 * The model representation of the feature tree that notifies listeners of
 * changes in the tree.
 * 
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 * 
 */
// TODO #459 remove unnecessary initializations/calculations especially after clone()
public class FeatureModel implements PropertyConstants {

	public static final String COMPOSER_KEY = "composer";
	public static final QualifiedName composerConfigID = new QualifiedName(
			"featureproject.configs", "composer");
	public static final QualifiedName sourceFolderConfigID = new QualifiedName(
			"featureproject.configs", "source");
	public static final String SOURCE_ARGUMENT = "source";
	public static final String DEFAULT_SOURCE_PATH = "src";
	public static final String BUILDER_ID = "de.ovgu.featureide.core"
			+ ".extensibleFeatureProjectBuilder";
	/**
	 * the root feature
	 */
	protected Feature root;
//	private boolean autoLayoutLegend = true;
//	private boolean showHiddenFeatures = true;
//	private boolean hasVerticalLayout = true;
//	private FMPoint legendPos = new FMPoint(0, 0);
	/**
	 * a {@link Hashtable} containing all features
	 */
	protected Hashtable<String, Feature> featureTable = new Hashtable<String, Feature>();

	/**
	 * all comment lines from the model file without line number at which they
	 * occur
	 */

//	private int selectedLayoutAlgorithm = 1;

	protected LinkedList<String> comments = new LinkedList<String>();

	/**
	 * 
	 */
	protected LinkedList<Node> propNodes = new LinkedList<Node>();
	
	/*
	 * TODO #461 why are constraints saved redundant
	 */
	protected LinkedList<Constraint> constraints = new LinkedList<Constraint>();

	/**
	 * This string saves the annotations from the model file as they were read,
	 * because they were not yet used.
	 */
	protected LinkedList<String> annotations = new LinkedList<String>();

	/**
	 * a list containing all renamings since the last save
	 */
	private LinkedList<Renaming> renamings = new LinkedList<Renaming>();

	/**
	 * a list containing the feature names in their specified order will be
	 * initialized in XmlFeatureModelReader
	 */
	private List<String> featureOrderList = new LinkedList<String>();
	private boolean featureOrderUserDefined = false;
	private boolean featureOrderInXML = false;

	private IFolder sourceFolder;

	private IFMComposerExtension fmComposerExtension = new FMComposerExtension();
	private String COMPOSER_ID;
	
	private Object undoContext;

	private final LinkedList<PropertyChangeListener> listenerList = new LinkedList<PropertyChangeListener>();
	protected ColorschemeTable colorschemeTable = new ColorschemeTable(this);
	protected boolean valid = true;
    private FeatureModelAnalyzer analyser = new FeatureModelAnalyzer(this);
    private FeatureModelLayout layout = new FeatureModelLayout();
	private LinkedList<Feature> falseOptionalFeatures = new LinkedList<Feature>();
	private LinkedList<Feature> deadFeatures = new LinkedList<Feature>();

	/**
	 * @return the featureTable
	 */
	public Hashtable<String, Feature> getFeatureTable() {
		return featureTable;
	}

	/**
	 * @param featureTable
	 *            the featureTable to set
	 */
	public void setFeatureTable(Hashtable<String, Feature> featureTable) {
		this.featureTable = featureTable;
	}
	
	/**
	 * 
	 * 		this should be done at the constructor
	 * 
	 * @return the fMComposerExtension
	 */
//	TODO @Jens description / rename
	public IFMComposerExtension getFMComposerExtension(IProject project) {
		setComposerID(project);
		setComposer();
		return fmComposerExtension;
	}

	public boolean isFeatureModelingComposer() {
		if (COMPOSER_ID == null) return true;
		return COMPOSER_ID.endsWith("FeatureModeling");
		// TODO #455 wrong usage of composer extension
	}
	
	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelLayout#setLayout(int)} instead.
	 */
	@Deprecated
	public void setLayout(int newLayoutAlgorithm) {
	    layout.setLayout(newLayoutAlgorithm);
	}

	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelLayout#getLayoutAlgorithm()} instead.
	 */
	@Deprecated
	public int getLayoutAlgorithm() {
	    return layout.getLayoutAlgorithm();
	}

	public static void setFeatureLocation(FMPoint newLocation, Feature feature) {
		feature.setNewLocation(newLocation);
	}

	public void reset() {
		if (root != null) {
			while (root.hasChildren()) {
				Feature child = root.getLastChild();
				deleteChildFeatures(child);
				root.removeChild(child);
				featureTable.remove(child.getName());
			}
			root = null;
		}
		featureTable.clear();
		renamings.clear();
		propNodes.clear();
		constraints.clear();
		comments.clear();
		annotations.clear();
		featureOrderList.clear();
		colorschemeTable.reset();
	}

	private void deleteChildFeatures(Feature feature) {
		while (feature.hasChildren()) {
			Feature child = feature.getLastChild();
			deleteChildFeatures(child);
			feature.removeChild(child);
			featureTable.remove(child.getName());
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
		if (propNodes.contains(node)) {
			propNodes.remove(node);
			constraints.remove(constraints.size() - 1);
		}
	}
	
	/*
	 * It is neccassary to remove the same object and not an equivalent one.
	 */
	public void removePropositionalNode(Constraint constraint) {
		int i = 0;
		for (Constraint c : constraints) {
			if (c == constraint) {
				constraints.remove(i);
				propNodes.remove(i);
				return;
			}
			i++;
		}
		
		if (propNodes.contains(constraint.getNode())) {
			propNodes.remove(constraint.getNode());
			constraints.remove(constraint);
		}
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
		
		// remove feature from order list
		for (int i = 0;i < featureOrderList.size();i++) {
			if (featureOrderList.get(i).equals(name)) {
				featureOrderList.remove(i);
				break;
			}
		}
		return true;
	}

	@CheckForNull
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
		
		// update the feature order list
		for (int i = 0;i < featureOrderList.size();i++) {
			if (featureOrderList.get(i).equals(oldName)) {
				featureOrderList.set(i, newName);
				break;
			}
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
		IProject project = ((IResource) file.getAdapter(IFile.class))
				.getProject();
		String sourceName = getProjectConfigurationPath(project);
		if (!"".equals(sourceName)) {
			sourceFolder = project.getFolder(sourceName);
		}
		for (Renaming renaming : renamings) {
			if (!performComposerRenamings(renaming.oldName, renaming.newName,
					project)) {
				moveFolder(renaming.oldName, renaming.newName);
			}
		}

		colorschemeTable.readColorsFromFile(project);
		colorschemeTable.saveColorsToFile(project);
		renamings.clear();
	}

	private boolean performComposerRenamings(final String oldName,
			final String newName, final IProject project) {
		return getFMComposerExtension(project).performRenaming(oldName,	newName, project);
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

	public void addListener(PropertyChangeListener listener) {
		if (!listenerList.contains(listener))
			listenerList.add(listener);
	}

	public void removeListener(PropertyChangeListener listener) {
		listenerList.remove(listener);
	}

	public void handleModelDataLoaded() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				MODEL_DATA_LOADED, Boolean.FALSE, Boolean.TRUE);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}

	public void handleModelDataChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				MODEL_DATA_CHANGED, Boolean.FALSE, Boolean.TRUE);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}
	
	public void handleModelLayoutChanged() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				MODEL_LAYOUT_CHANGED, Boolean.FALSE, Boolean.TRUE);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}
	
	public void refreshContextMenu() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				REFRESH_ACTIONS, Boolean.FALSE, Boolean.TRUE);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}
	/**
	 * Use {@link FeatureModel#handleModelDataChanged()} instead to refresh the diagram.
	 */
	@Deprecated
	public void redrawDiagram() {
		PropertyChangeEvent event = new PropertyChangeEvent(this,
				REDRAW_DIAGRAM, Boolean.FALSE, Boolean.TRUE);
		for (PropertyChangeListener listener : listenerList)
			listener.propertyChange(event);
	}
	
//	public void handleFeatureNameChanged() {
//		PropertyChangeEvent event = new PropertyChangeEvent(this,
//				FEATURE_NAME_CHANGED, Boolean.FALSE, Boolean.TRUE);
//		for (PropertyChangeListener listener : listenerList)
//			listener.propertyChange(event);
//	}

	/**
	 * Returns the value calculated during the last call of
	 * updateFeatureModel().
	 * 
	 * @return cached value
	 */
	public boolean valid() {
		return valid;
	}
	
    /**
     * 
     * @return Hashmap: key entry is Feature/Constraint, value usually indicating the kind of attribute
     * 
     * 	if Feature 
     * 
     * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#analyzeFeatureModel()} instead. 
     */
	@Deprecated
	public HashMap<Object, Object> analyzeFeatureModel() {
	    return analyser.analyzeFeatureModel(null);
	}

	public Collection<Feature> getFeatures() {
		return new ArrayList<Feature>(featureTable.values());
	}

	/**
	 * 
	 * @return A list of all concrete features. This list is in preorder of the tree. 
	 */
	@Nonnull
	public Collection<Feature> getConcreteFeatures() {
		LinkedList<Feature> concreteFeatures = new LinkedList<Feature>();
		if (root != null) {
			initFeatures(root, concreteFeatures);
		}
		return Collections.unmodifiableCollection(concreteFeatures);
	}

	private void initFeatures(Feature feature, LinkedList<Feature> concreteFeatures) {
		if (feature.isConcrete()) {
			concreteFeatures.add(feature);
		}
		for (Feature child : feature.getChildren()) {
			initFeatures(child, concreteFeatures);
		}
	}

	/**
	 * 
	 * @return A list of all concrete feature names. This list is in preorder of the tree. 
	 */
	@Nonnull
	public LinkedList<String> getConcreteFeatureNames() {
		LinkedList<String> concreteFeatureNames = new LinkedList<String>();
		for (Feature f : getConcreteFeatures()) {
			concreteFeatureNames.add(f.getName());
		}
		return concreteFeatureNames;
	}

	public void createDefaultValues(String projectName) {
		String rootName = getValidJavaIdentifier(projectName);
		Feature root;
		if (!"".equals(rootName)) {
			root = getFeature(rootName);
		} else {
			root = getFeature("Root");
		}
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

	public void replacePropNode(int index, Node node) {
		assert (index < constraints.size());
		constraints.set(index, new Constraint(this, node));
		propNodes.set(index, node);
	}

	public int getNumberOfFeatures() {
		return featureTable.size();
	}

	@Override
	public FeatureModel clone() {
		FeatureModel fm = new FeatureModel();
		fm.root = root != null ? root.clone() : new Feature(fm, "Root");
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
		fm.colorschemeTable = colorschemeTable.clone(fm);
		return fm;
	}

	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#isValid()} instead.
	 */
	@Deprecated
	public boolean isValid() throws TimeoutException {
	    return analyser.isValid();
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
	 * 
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#checkImplies(Set, Set)} instead.
	 */
	@Deprecated
	public boolean checkImplies(Set<Feature> a, Set<Feature> b)
			throws TimeoutException {
	    	return analyser.checkImplies(a, b);
	}

	/**
	 * checks some condition against the feature model. use only if you know
	 * what you are doing!
	 * 
	 * @return
	 * @throws TimeoutException
	 * 
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#checkCondition(Node)} instead.
	 */
	@Deprecated
	public boolean checkCondition(Node condition) {
	    	return analyser.checkCondition(condition);
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
	 * 
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#areMutualExclusive(Set, List)} instead.
	 */
	@Deprecated
	public boolean areMutualExclusive(Set<Feature> context,
			List<Set<Feature>> featureSets) throws TimeoutException {
	    	return analyser.areMutualExclusive(context, featureSets);
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
	 * 
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#mayBeMissing(Set, List)} instead.
	 */
	@Deprecated
	public boolean mayBeMissing(Set<Feature> context,
			List<Set<Feature>> featureSets) throws TimeoutException {
		return analyser.mayBeMissing(context, featureSets);
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
	 * 
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#exists(Set)} instead.
	 */
	@Deprecated
	public boolean exists(Set<Feature> features) throws TimeoutException {
	    	return analyser.exists(features);
	}

	/**
	 * 
	 * @param b
	 * @return
	 * 
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#conjunct(Set)} instead.
	 */
	@Deprecated
	public Node conjunct(Set<Feature> b) {
	    	return analyser.conjunct(b);
	}

	/**
	 * 
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#countConcreteFeatures()} instead.
	 */
	@Deprecated
	public int countConcreteFeatures() {
	    return analyser.countConcreteFeatures();
	}

	/**
	 * 
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#countHiddenFeatures()} instead.
	 */
	@Deprecated
	public int countHiddenFeatures() {
	    return analyser.countHiddenFeatures();
	}

	/**
	 * 
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#countTerminalFeatures()} instead.
	 */
	@Deprecated
	public int countTerminalFeatures() {
	    return analyser.countTerminalFeatures();
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
	 * 
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#commonFeatures(long, Object...)} instead.
	 */
	@Deprecated
	public LinkedList<String> commonFeatures(long timeout,
			Object... selectedFeatures) {
	    	return analyser.commonFeatures(timeout, selectedFeatures);
	}

	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelAnalyzer#getDeadFeatures()} instead.
	 */
	@Deprecated
	public LinkedList<Feature> getDeadFeatures() {
	    	return analyser.getDeadFeatures();
	}

	/**
	 * Checks a string to be a valid featurename.
	 * 
	 * @param s Possible featurename to be checked
	 * @return boolean
	 */
	public boolean isValidFeatureName(String s) {
		return fmComposerExtension.isValidFeatureName(s);
	}
	
	/**
	 * Removes all invalid java identifiers form a given string.
	 */
	private String getValidJavaIdentifier(String s) {
		StringBuilder stringBuilder = new StringBuilder();
		int i = 0;
		for (; i < s.length(); i++) {
			if (Character.isJavaIdentifierStart(s.charAt(i))) {
				stringBuilder.append(s.charAt(i));
				i++;
				break;
			}
		}
		for (; i < s.length(); i++) {
			if (Character.isJavaIdentifierPart(s.charAt(i))) {
				stringBuilder.append(s.charAt(i));
			}
		}
		return stringBuilder.toString();
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
				if (BUILDER_ID.equals(command.getBuilderName())) {
					return (String) command.getArguments().get(argument);
				}
			}
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return null;
	}

	/**
	 * for unit testing purposes only
	 * @param s
	 */
	public void setComposerID(String s, Object o) {
		COMPOSER_ID = s;
		fmComposerExtension = (IFMComposerExtension)o;
		/*final FeatureModelingFMExtension f;// = new FMComposerExtension();
		fmComposerExtension =  (IFMComposerExtension)f;*/
		//setComposer();
	}
	
	
	private void setComposerID(IProject project) {
		if(project==null)return;
		try {
			String id = project.getPersistentProperty(composerConfigID);
			if (id != null) {
				COMPOSER_ID = id;
				return;
			}
			
			
			for (ICommand command : project.getDescription().getBuildSpec()) {
				if (BUILDER_ID.equals(command.getBuilderName())) {
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
				.getConfigurationElementsFor(
						FMCorePlugin.PLUGIN_ID + ".FMComposer");
		try {
			for (IConfigurationElement e : config) {
				if (e.getAttribute("composer").equals(COMPOSER_ID)) {
					final Object o = e.createExecutableExtension("class");
					if (o instanceof IFMComposerExtension) {
						fmComposerExtension = (IFMComposerExtension) o;
					}
				}
			}
		} catch (Exception e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelLayout#getLegendPos()} instead.
	 */
	@Deprecated
	public FMPoint getLegendPos() {
	    return layout.getLegendPos();
	}

	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelLayout#setLegendPos(int, int)} instead.
	 */
	@Deprecated
	public void setLegendPos(int x, int y) {
	    layout.setLegendPos(x, y);
	}

	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelLayout#setLegendAutoLayout(boolean)} instead.
	 */
	@Deprecated
	public void setLegendAutoLayout(boolean b) {
	    layout.setLegendAutoLayout(b);
	}

	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelLayout#hasLegendAutoLayout()} instead.
	 */
	@Deprecated
	public boolean hasLegendAutoLayout() {
	    return layout.hasLegendAutoLayout();
	}

	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelLayout#hasFeaturesAutoLayout()} instead.
	 */
	@Deprecated
	public boolean hasFeaturesAutoLayout() {
	    return layout.hasFeaturesAutoLayout();
	}

	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelLayout#showHiddenFeatures()} instead.
	 */
	@Deprecated
	public boolean showHiddenFeatures() {
	    return layout.showHiddenFeatures();
	}

	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelLayout#showHiddenFeatures(boolean)} instead.
	 */
	@Deprecated
	public void showHiddenFeatures(boolean b) {
	    layout.showHiddenFeatures(b);
	}

	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelLayout#verticalLayout()} instead.
	 */
	@Deprecated
	public boolean verticalLayout() {
	    return layout.verticalLayout();
	}

	/**
	 * @Deprecated Will be removed in a future release. Use {@link FeatureModelLayout#verticalLayout(boolean)} instead.
	 */
	@Deprecated
	public void verticalLayout(boolean b) {
	    layout.verticalLayout(b);
	}

	/**
	 * @return true if feature model contains mandatory features otherwise false
	 */
	public boolean hasMandatoryFeatures() {
		for (Feature f : featureTable.values()) {
			Feature parent = f.getParent();
			if (parent != null && parent.isAnd() && f.isMandatory())
				return true;
		}
		return false;
	}

	/**
	 * @return <code>true</code> if feature model contains optional features otherwise false
	 */
	public boolean hasOptionalFeatures() {
		for (Feature f : featureTable.values()) {
			if (!f.equals(root) && f.getParent().isAnd()
					&& !f.isMandatory())
				return true;
		}
		return false;
	}

	/**
	 * @return true if feature model contains and group otherwise false
	 */
	public boolean hasAndGroup() {
		for (Feature f : featureTable.values()) {
			if (f.getChildrenCount() > 1 && f.isAnd())
				return true;
		}
		return false;
	}

	/**
	 * @return true if feature model contains alternative group otherwise false
	 */
	public boolean hasAlternativeGroup() {
		for (Feature f : featureTable.values()) {
			if (f.getChildrenCount() > 1 && f.isAlternative())
				return true;
		}
		return false;
	}
	
	/**
	 * @return true if feature model contains or group otherwise false
	 */
	public boolean hasOrGroup() {
		for (Feature f : featureTable.values()) {
			if (f.getChildrenCount() > 1 && f.isOr())
				return true;
		}
		return false;
	}

	public boolean hasAbstract() {
		for (Feature f : featureTable.values()) {
			if (f.isAbstract())
				return true;
		}
		return false;
	}

	public boolean hasConcrete() {
		for (Feature f : featureTable.values()) {
			if (!(f.isAbstract()))
				return true;
		}
		return false;
	}

	/**
	 * 
	 * @return <code>true</code> if the feature model contains a hidden feature
	 */
	/*
	 * TODO sometimes this method returns false while the model has hidden features 	
	 * 		the model seems to be initialized wrong 
	 */
	public boolean hasHidden() {
		for (Feature f : new ArrayList<Feature>(featureTable.values())) {
			if (f.isHidden())
				return true;
		}
		return false;
	}

	public boolean hasDead() {
		return this.getDeadFeatures().size() > 0;
	}
	
	public boolean hasIndetHidden() {
		for (Feature f : featureTable.values()) {
			if (f.getFeatureStatus() == FeatureStatus.INDETERMINATE_HIDDEN)
				return true;
		}
		return false;
	}
	
	public boolean hasUnsatisfiableConst() {
		for (Constraint c : constraints) {
			if (c.getConstraintAttribute() == ConstraintAttribute.UNSATISFIABLE)
				return true;
		}
		return false;
	}
	
	public boolean hasTautologyConst() {
		for (Constraint c : constraints) {
			if (c.getConstraintAttribute() == ConstraintAttribute.TAUTOLOGY)
				return true;
		}
		return false;
	}
	public boolean hasDeadConst() {
		for (Constraint c : constraints) {
			if (c.getConstraintAttribute() == ConstraintAttribute.DEAD)
				return true;
		}
		return false;
	}
	
	public boolean hasVoidModelConst() {
		for (Constraint c : constraints) {
			if (c.getConstraintAttribute() == ConstraintAttribute.VOID_MODEL)
				return true;
		}
		return false;
	}
	
	public boolean hasRedundantConst() {
		for (Constraint c : this.constraints) {
			if (c.getConstraintAttribute() == ConstraintAttribute.REDUNDANT)
				return true;
		}
		return false;
	}


	public boolean hasFalse() {
		for (Feature f : featureTable.values()) {
			if (f.getFeatureStatus() == FeatureStatus.FALSE_OPTIONAL)
				return true;
		}
		return false;
	}

	public void setUndoContext(Object undoContext) {
		this.undoContext = undoContext;
	}
	
	/**
	 * @return
	 */
	public Object getUndoContext() {
		return undoContext;
	}

	public void setConstraints(LinkedList<Constraint> constraints) {
		this.constraints = constraints;
		this.propNodes = new LinkedList<Node>();
		for (Constraint c : constraints) {
			propNodes.add(c.getNode());
		}
	}

	/**
	 * @param constraint
	 */
	public int getConstraintIndex(Constraint constraint) {
		int j = 0;
		for (Constraint c : constraints) {
			if (constraint == c) {
				return j;
			}
			j++;
		}
		return -1;
	}

	/**
	 * @param node
	 * @param constraintIndex
	 */
	public void addPropositionalNode(Node node, int index) {
		constraints.add(index, new Constraint(this, node));
		propNodes.add(index, node);
	}
	
	public void addConstraint(Constraint constraint, int index) {
		constraints.add(index, constraint);
		propNodes.add(index, constraint.getNode());
	}

	
	/**
	 * @return the featureOrderList
	 */
	public List<String> getFeatureOrderList() {
		return featureOrderList;
	}

	/**
	 * @param featureOrderList
	 *            the featureOrderList to set
	 */
	public void setFeatureOrderList(List<String> featureOrderList) {
		this.featureOrderList = featureOrderList;
	}

	/**
	 * @return the featureOrderUserDefined
	 */
	public boolean isFeatureOrderUserDefined() {
		return featureOrderUserDefined;
	}

	/**
	 * @param featureOrderUserDefined
	 *            the featureOrderUserDefined to set
	 */
	public void setFeatureOrderUserDefined(boolean featureOrderUserDefined) {
		this.featureOrderUserDefined = featureOrderUserDefined;
	}

	/**
	 * @return the featureOrderInXML
	 */
	public boolean isFeatureOrderInXML() {
		return featureOrderInXML;
	}

	/**
	 * @param featureOrderInXML
	 *            the featureOrderInXML to set
	 */
	public void setFeatureOrderInXML(boolean featureOrderInXML) {
		this.featureOrderInXML = featureOrderInXML;
	}
	
    public FeatureModelAnalyzer getAnalyser() {
    	return analyser;
    }

	/**
	 * @return the falseOptionalFeatures
	 */
	public LinkedList<Feature> getFalseOptionalFeatures() {
		return falseOptionalFeatures;
	}

    public FeatureModelLayout getLayout() {
    	return layout;
    }

	/**
	 * @return the dead features
	 */
	public LinkedList<Feature> getCalculatedDeadFeatures() {
		return deadFeatures;
	}

	/**
	 * @return the colorschemeTable
	 */
	public ColorschemeTable getColorschemeTable() {
		return colorschemeTable;
	}

	/**
	 * @param constraint
	 */
	public void addConstraint(Constraint constraint) {
		propNodes.add(constraint.getNode());
		constraints.add(constraint);
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return print(this);
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