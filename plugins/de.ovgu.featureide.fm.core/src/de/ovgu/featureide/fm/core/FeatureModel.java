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
package de.ovgu.featureide.fm.core;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentLinkedQueue;

import javax.annotation.CheckForNull;
import javax.annotation.Nonnull;

import org.eclipse.core.resources.IProject;
import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.job.AStoppableJob;
import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * The model representation of the feature tree that notifies listeners of
 * changes in the tree.
 * 
 * @author Thomas Thuem
 * @author Florian Proksch
 * @author Stefan Krueger
 * 
 */
public class FeatureModel extends DeprecatedFeatureModel implements PropertyConstants {
	
	private Feature rootFeature;
	
	/**
	 * A {@link Map} containing all features.
	 */
	private final Map<String, Feature> featureTable = new ConcurrentHashMap<String, Feature>();

	protected final List<Constraint> constraints = new LinkedList<Constraint>();
	
	private final List<PropertyChangeListener> listenerList = new LinkedList<PropertyChangeListener>();
	
	private final FeatureModelAnalyzer analyser = createAnalyser();
	
	private final RenamingsManager renamingsManager = new RenamingsManager(this);
	
	/**
	 * All comment lines from the model file without line number at which they
	 * occur
	 */
	private final List<String> comments;
	
	/**
	 * Saves the annotations from the model file as they were read,
	 * because they were not yet used.
	 */
	private final List<String> annotations;
	
	/**
	 * A list containing the feature names in their specified order will be
	 * initialized in XmlFeatureModelReader.
	 */
	private final List<String> featureOrderList;
	
	private final FeatureModelLayout layout;
	
	private boolean featureOrderUserDefined;
	
	private boolean featureOrderInXML;
	
	private Object undoContext;
	
	private ColorschemeTable colorschemeTable;

	private FMComposerManager fmComposerManager;
	
	public FeatureModel() {
		super();

		this.featureOrderList = new LinkedList<String>();
		this.featureOrderUserDefined = false;
		this.featureOrderInXML = false;
		
		this.comments = new LinkedList<String>();
		this.annotations = new LinkedList<String>();
		this.colorschemeTable = new ColorschemeTable(this);
		this.layout = new FeatureModelLayout();
	}

	protected FeatureModel(FeatureModel oldFeatureModel, boolean complete) {
		super();
		
		this.featureOrderList = new LinkedList<String>(oldFeatureModel.featureOrderList);
		this.featureOrderUserDefined = oldFeatureModel.featureOrderUserDefined;
		this.featureOrderInXML = oldFeatureModel.featureOrderInXML;
		
		if (complete) {
			this.annotations = new LinkedList<String>(oldFeatureModel.annotations);
			this.comments = new LinkedList<String>(oldFeatureModel.comments);
			this.colorschemeTable = oldFeatureModel.colorschemeTable.clone(this);
			this.layout = oldFeatureModel.layout.clone();
		} else {
			this.annotations = null;
			this.comments = null;
			this.colorschemeTable = null;
			this.layout = null;
		}
		
		if (oldFeatureModel.rootFeature != null) {
			this.rootFeature = oldFeatureModel.rootFeature.clone(this, complete);
			
			for (final Constraint constraint : oldFeatureModel.constraints) {
				this.addConstraint(new Constraint(this, constraint.getNode().clone()));
			}
		}		
	}
	
	protected FeatureModelAnalyzer createAnalyser() {
		return new FeatureModelAnalyzer(this);
	}
	/**
	 * Returns the {@link FeatureModelAnalyzer} which should be used for all calculation 
	 * on the {@link FeatureModel}.
	 */
	@Override
    public FeatureModelAnalyzer getAnalyser() {
    	return analyser;
    }

	@Override
    public FeatureModelLayout getLayout() {
		return layout;
    }

	public ColorschemeTable getColorschemeTable() {
		return colorschemeTable;
	}
	
	@Override
	public FMComposerManager getFMComposerManager(final IProject project) {
		if (fmComposerManager == null) {
			fmComposerManager = new FMComposerManager(project);
		}
		return fmComposerManager;
	}

	public IFMComposerExtension initFMComposerExtension(final IProject project) {
		return getFMComposerManager(project);
	}

	public IFMComposerExtension getFMComposerExtension() {
		return getFMComposerManager(null).getFMComposerExtension();
	}
	
	@Override
	public RenamingsManager getRenamingsManager() {
		return renamingsManager;
	}
	
	public void reset() {
		if (rootFeature != null) {
			while (rootFeature.hasChildren()) {
				Feature child = rootFeature.getLastChild();
				deleteChildFeatures(child);
				rootFeature.removeChild(child);
				featureTable.remove(child.getName());
			}
			rootFeature = null;
		}
		featureTable.clear();
		renamingsManager.clear();
		constraints.clear();
		if (comments != null) {
			comments.clear();
		}
		if (annotations != null) {
			annotations.clear();
		}
		if (colorschemeTable != null) {
			colorschemeTable.reset();
		}
		featureOrderList.clear();
	}
	
	private void deleteChildFeatures(Feature feature) {
		while (feature.hasChildren()) {
			Feature child = feature.getLastChild();
			deleteChildFeatures(child);
			feature.removeChild(child);
			featureTable.remove(child.getName());
		}
	}
	
	/**
	 * Creates a default {@link FeatureModel} with a root feature named as the project and a
	 * child feature named base.
	 * @param projectName The name of the project
	 */
	public void createDefaultValues(String projectName) {
		String rootName = getValidJavaIdentifier(projectName);
		if (rootName.isEmpty()) {
			rootName = "Root";
		}		
		if (featureTable.isEmpty()) {
			rootFeature = new Feature(this, rootName);
			addFeature(rootFeature);
		}
		Feature feature = new Feature(this, "Base");
		addFeature(feature);
		
		rootFeature.addChild(feature);
		rootFeature.setAbstract(true);
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

	/* *****************************************************************
	 * 
	 * Feature handling
	 * 
	 *******************************************************************/
	public void setRoot(Feature root) {
		this.rootFeature = root;
	}
	
	public Feature getRoot() {
		return rootFeature;
	}

	/**
	 * @param featureTable
	 *            the featureTable to set
	 */
	public void setFeatureTable(final Hashtable<String, Feature> featureTable) {
		this.featureTable.clear();
		this.featureTable.putAll(featureTable);
	}
	
	public boolean addFeature(Feature feature) {
		String name = feature.getName();
		if (featureTable.containsKey(name))
			return false;
		featureTable.put(name, feature);
		return true;
	}
	
	public Collection<Feature> getFeatures() {
		return Collections.unmodifiableCollection(featureTable.values());
	}
	
	/**
	 * @return The {@link Feature} with the given name or {@code null} if there is no feature with this name. 
	 */
	@CheckForNull
	public Feature getFeature(String name) {
		return featureTable.get(name);
	}

	/**
	 * 
	 * @return A list of all concrete features. This list is in preorder of the tree. 
	 */
	@Nonnull
	public Collection<Feature> getConcreteFeatures() {
		List<Feature> concreteFeatures = new LinkedList<Feature>();
		if (rootFeature != null) {
			getConcreteFeatures(rootFeature, concreteFeatures);
		}
		return Collections.unmodifiableCollection(concreteFeatures);
	}

	private void getConcreteFeatures(Feature feature, List<Feature> concreteFeatures) {
		if (feature.isConcrete()) {
			concreteFeatures.add(feature);
		}
		for (Feature child : feature.getChildren()) {
			getConcreteFeatures(child, concreteFeatures);
		}
	}
	
	/**
	 * 
	 * @return A list of all concrete feature names. This list is in preorder of the tree. 
	 */
	@Nonnull
	public List<String> getConcreteFeatureNames() {
		List<String> concreteFeatureNames = new LinkedList<String>();
		for (Feature f : getConcreteFeatures()) {
			concreteFeatureNames.add(f.getName());
		}
		return concreteFeatureNames;
	}
	
	public Collection<Feature> getFeaturesPreorder() {
		List<Feature> preorderFeatures = new LinkedList<Feature>();
		if (rootFeature != null) {
			getFeaturesPreorder(rootFeature, preorderFeatures);
		}
		return Collections.unmodifiableCollection(preorderFeatures);
	}

	private void getFeaturesPreorder(Feature feature, List<Feature> preorderFeatures) {
		
		preorderFeatures.add(feature);
		for (Feature child : feature.getChildren()) {
			getFeaturesPreorder(child, preorderFeatures);
		}
	}
	
	public List<String> getFeatureNamesPreorder() {
		List<String> preorderFeaturesNames = new LinkedList<String>();
		for (Feature f : getFeaturesPreorder()) {
			preorderFeaturesNames.add(f.getName());
		}
		return preorderFeaturesNames;
	}
	
	/**
	 * @return <code>true</code> if a feature with the given name exists and is concrete.
	 * @deprecated Will be removed in a future release. Use {@link #getFeature(String)}.isConcrete() instead.
	 */
	@Deprecated
	public boolean isConcrete(String featureName) {
		Feature feature = featureTable.get(featureName);
		return feature != null && feature.isConcrete();
	}
	
	/**
	 * @return the featureTable
	 */
	protected Map<String, Feature> getFeatureTable() {
		return featureTable;
	}
	
	public Set<String> getFeatureNames() {
		return Collections.unmodifiableSet(featureTable.keySet());
	}
	
	public int getNumberOfFeatures() {
		return featureTable.size();
	}

	public void deleteFeatureFromTable(Feature feature) {
		featureTable.remove(feature.getName());
	}

	public boolean deleteFeature(Feature feature) {
		// the root can not be deleted
		if (feature == rootFeature) {
			return false;
		}

		// check if it exists
		String name = feature.getName();
		if (!featureTable.containsKey(name)) {
			return false;
		}

		// use the group type of the feature to delete
		Feature parent = feature.getParent();

		if (parent.getChildrenCount() == 1) {
			if (feature.isAnd()) {
				parent.setAnd();
			} else if (feature.isAlternative()) {
				parent.setAlternative();
			} else {
				parent.setOr();
			}
		}

		// add children to parent
		int index = parent.getChildIndex(feature);
		while (feature.hasChildren()) {
			parent.addChildAtPosition(index, feature.removeLastChild());
		}

		// delete feature
		parent.removeChild(feature);
		featureTable.remove(name);
		featureOrderList.remove(name);
		return true;
	}
	
	public void replaceRoot(Feature feature) {
		featureTable.remove(rootFeature.getName());
		rootFeature = feature;
	}

	/* *****************************************************************
	 * 
	 * Constraint handling
	 * 
	 *#*****************************************************************/
	public void setConstraints(final LinkedList<Constraint> constraints) {
		this.constraints.clear();
		this.constraints.addAll(constraints);
	}
	
	public void addPropositionalNode(Node node) {
		addConstraint(new Constraint(this, node));
	}
	
	public void addConstraint(Constraint constraint) {
		constraints.add(constraint);
	}

	public void addPropositionalNode(Node node, int index) {
		addConstraint(new Constraint(this, node), index);
	}
	
	public void addConstraint(Constraint constraint, int index) {
		constraints.add(index, constraint);
	}
	
	public List<Node> getPropositionalNodes() {
		LinkedList<Node> nodes = new LinkedList<Node>();
		for (Constraint c : constraints) {
			nodes.add(c.getNode());
		}
		return Collections.unmodifiableList(nodes);
	}
	
	public Node getConstraint(int index) {
		return constraints.get(index).getNode();
	}
	                                                                                                                                                                                                                                                                                                                                                                                                                                                                     
	public List<Constraint> getConstraints() {
		return Collections.unmodifiableList(constraints);
	}

	/**
	 * 
	 * @param constraint
	 * @return The position of the given {@link Constraint} or 
	 * 			-1 if it does not exist.
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

	public void removePropositionalNode(Node node) {
		for (Constraint c : constraints) {
			if (c.getNode().equals(node)) {
				removeConstraint(c);
				break;
			}
		}
	}

	public void removeConstraint(Constraint constraint) {
		constraints.remove(constraint);
	}

	public void removeConstraint(int index) {
		constraints.remove(index);
	}
	
	public void replacePropNode(int index, Node node) {
		assert (index < constraints.size());
		constraints.set(index, new Constraint(this, node));
	}
	
	public int getConstraintCount() {
		return constraints.size();
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
	
	public void addListener(PropertyChangeListener listener) {
		if (!listenerList.contains(listener)) {
			listenerList.add(listener);
		}
	}

	public void removeListener(PropertyChangeListener listener) {
		listenerList.remove(listener);
	}
	
	public void handleModelDataLoaded() {
		fireEvent(MODEL_DATA_LOADED);
	}

	public void handleModelDataChanged() {
		fireEvent(MODEL_DATA_CHANGED);
	}
	
	public void handleModelLayoutChanged() {
		fireEvent(MODEL_LAYOUT_CHANGED);
	}
	
	public void handleLegendLayoutChanged() {
		fireEvent(LEGEND_LAYOUT_CHANGED);
	}
	
	public void refreshContextMenu() {
		fireEvent(REFRESH_ACTIONS);
	}
	/**
	 * Refreshes the diagram colors.
	 */
	public void redrawDiagram() {
		fireEvent(REDRAW_DIAGRAM);
	}
	
	private final void fireEvent(final String action) {
		final PropertyChangeEvent event = new PropertyChangeEvent(this,
				action, Boolean.FALSE, Boolean.TRUE);
		for (PropertyChangeListener listener : listenerList) {
			listener.propertyChange(event);
		}
	}
	
	@Override
	public FeatureModel clone() {
		final FeatureModel clone = new FeatureModel();
		clone.featureTable.putAll(featureTable);
		if (rootFeature == null) {
			// TODO this should never happen
			clone.rootFeature = new Feature(clone, "Root");
			clone.featureTable.put("root", clone.rootFeature);
		} else {
			clone.rootFeature = clone.getFeature(rootFeature.getName());
		}
		clone.constraints.addAll(constraints);
		clone.annotations.addAll(annotations);
		clone.comments.addAll(comments);
		clone.colorschemeTable = colorschemeTable.clone(clone);
		return clone;
	}
	
	/**
	 * Will return the value of clone(true).
	 * @return a deep copy from the feature model
	 * 
	 * @see #clone(boolean)
	 */
	public FeatureModel deepClone() {
		return deepClone(true);
	}
	
	/**
	 * Clones the feature model.
	 * Makes a deep copy from all fields in the model.</br>
	 * Note that: {@code fm == fm.clone(false)} and {@code fm == fm.clone(true)} are {@code false} in every case.
	 * 
	 * @param complete If {@code false} the fields annotations, comments, colorschemeTable and layout
	 * are set to {@code null} for a faster cloning process.
	 * @return a deep copy from the feature model
	 * 
	 * @see #clone()
	 */
	public FeatureModel deepClone(boolean complete) {
		return new FeatureModel(this, complete);
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
			if (!f.equals(rootFeature) && f.getParent().isAnd()
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
			if (f.isConcrete())
				return true;
		}
		return false;
	}
	
	/**
	 * @return number of or groups contained in the feature model
	 */
	public int numOrGroup() {
		int count = 0;
		for (Feature f : featureTable.values()) {
			if (f.getChildrenCount() > 1 && f.isOr()) {
				count++;
			}
		}
		return count;
	}
	
	public int numAlternativeGroup() {
		int count = 0;
		for (Feature f : featureTable.values()) {
			if (f.getChildrenCount() > 1 && f.isAlternative()) {
				count++;
			}
		}
		return count;
	}
	
	/**
	 * 
	 * @return <code>true</code> if the feature model contains a hidden feature
	 */
	public boolean hasHidden() {
		for (Feature f : featureTable.values()) {
			if (f.isHidden()) {
				return true;
			}
		}
		return false;
	}

	public boolean hasIndetHidden() {
		for (Feature f : featureTable.values()) {
			if (f.getFeatureStatus() == FeatureStatus.INDETERMINATE_HIDDEN) {
				return true;
			}
		}
		return false;
	}
	
	public boolean hasUnsatisfiableConst() {
		for (Constraint c : constraints) {
			if (c.getConstraintAttribute() == ConstraintAttribute.UNSATISFIABLE) {
				return true;
			}
		}
		return false;
	}
	
	public boolean hasTautologyConst() {
		for (Constraint c : constraints) {
			if (c.getConstraintAttribute() == ConstraintAttribute.TAUTOLOGY) {
				return true;
			}
		}
		return false;
	}
	public boolean hasDeadConst() {
		for (Constraint c : constraints) {
			if (c.getConstraintAttribute() == ConstraintAttribute.DEAD || !c.getDeadFeatures().isEmpty()) {
				return true;
			}
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
		for (Constraint c : constraints) {
			if (c.getConstraintAttribute() == ConstraintAttribute.REDUNDANT) {
				return true;
			}
		}
		return false;
	}


	public boolean hasFalseOptionalFeatures() {
		for (Feature f : featureTable.values()) {
			if (f.getFeatureStatus() == FeatureStatus.FALSE_OPTIONAL) {
				return true;
			}
		}
		return false;
	}

	public void setUndoContext(Object undoContext) {
		this.undoContext = undoContext;
	}

	public Object getUndoContext() {
		return undoContext;
	}

	public List<String> getFeatureOrderList() {
		if (featureOrderList.isEmpty()) {
			return getConcreteFeatureNames();
		}
		return featureOrderList;
	}

	public void setFeatureOrderList(final List<String> featureOrderList) {
		this.featureOrderList.clear();
		this.featureOrderList.addAll(featureOrderList);
	}

	public boolean isFeatureOrderUserDefined() {
		return featureOrderUserDefined;
	}

	public void setFeatureOrderUserDefined(boolean featureOrderUserDefined) {
		this.featureOrderUserDefined = featureOrderUserDefined;
	}

	public boolean isFeatureOrderInXML() {
		return featureOrderInXML;
	}

	public void setFeatureOrderInXML(boolean featureOrderInXML) {
		this.featureOrderInXML = featureOrderInXML;
	}
	
	@Override
	public String toString() {
		String x = "";
		try {
			x = toString(getRoot());
			for (Constraint c : getConstraints()) {
				x +=c.toString() + " ";
			}
		} catch (Exception e) {
			return "Empty Feature Model";
		}
		return x;
	}
	
	private String toString(Feature feature) {
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
				x += toString(child);
			} else {
				x += child.getName();
			}
		}
		return x + " ] ";
	}
	
	@Override
	public boolean equals(Object obj) {
		return obj == this;// TODO equals should be implemented
	}
	
	@Override
	public int hashCode() {
		int hash = 31;
		for (String f : featureOrderList) {
			hash = hash * 7 + f.hashCode();
		}
		for (Constraint c : constraints) {
			hash = hash * 7 + c.toString().hashCode();
		}
		return hash;
	}
	
	public void splitModel() {
		final IJob splittJob = new AStoppableJob("Spliting Feature Model") {
			private Collection<Feature> coreFeatures = null;
			private FeatureGraph featureGraph = null;
			
			@Override
			protected boolean work() throws Exception {
				System.out.println("Computing...");
				coreFeatures = getAnalyser().getCoreFeatures();
				final List<Constraint> constraints = getConstraints();
				final Collection<Feature> features = new LinkedList<Feature>(getFeatures());
				features.removeAll(coreFeatures);
				
				workMonitor.setMaxAbsoluteWork(features.size() + 2);
				
				featureGraph = new FeatureGraph(features);
				
				workMonitor.worked();
				
				for (Feature feature : features) {
					if (!coreFeatures.contains(feature.getParent())) {
						featureGraph.implies(feature.getName(), feature.getParent().getName());
						if (feature.getParent().isAnd() && feature.isMandatory()) {
							featureGraph.implies(feature.getParent().getName(), feature.getName());
						} else if (feature.getParent().isAlternative() || feature.getParent().isOr()) {
							featureGraph.setEdge(feature.getParent().getName(), feature.getName(), FeatureGraph.EDGE_1q);
							featureGraph.setEdge(feature.getName(), feature.getParent().getName(), FeatureGraph.EDGE_0q);
						} else if (feature.getParent().isAnd() && !feature.isMandatory()) {
							featureGraph.setEdge(feature.getName(), feature.getParent().getName(), FeatureGraph.EDGE_0q);
						}
					}
					if (feature.getParent().isAlternative()) {
						for (Feature sibiling : feature.getParent().getChildren()) {
							if (!coreFeatures.contains(sibiling)) {
								featureGraph.setEdge(feature.getName(), sibiling.getName(), FeatureGraph.EDGE_10);
								featureGraph.setEdge(feature.getName(), sibiling.getName(), FeatureGraph.EDGE_0q);
							}
						}
					} else if (feature.getParent().isOr()) {
						boolean optionalFeature = false;
						for (Feature sibiling : feature.getParent().getChildren()) {
							if (coreFeatures.contains(sibiling)) {
								optionalFeature = true;
								break;
							}
						}
						if (!optionalFeature) {
							for (Feature sibiling : feature.getParent().getChildren()) {
								featureGraph.setEdge(feature.getName(), sibiling.getName(), FeatureGraph.EDGE_0q);
							}
						}
					}
				}
				
				for (Constraint constraint : constraints) {
					connect(constraint.getNode());
				}
				
				featureGraph.clearDiagonal();
				
				workMonitor.worked();
				
				final ArrayList<String> featureNames = new ArrayList<>();
				for (Feature feature : features) {
					featureNames.add(feature.getName());
				}
				
				final DFSThreadPool dfsThreadPool = new DFSThreadPool(featureGraph, featureNames, workMonitor);
				dfsThreadPool.run();
				
				statistic();
				
				return true;
			}
			
			private void statistic() {
				// ----- 1 ---------------------------
					final int[] featureNeigbors = new int[featureGraph.featureArray.length];
					int i = 0;
					for (String feature : featureGraph.featureArray) {
						featureNeigbors[i++] = featureGraph.countNeighbors(feature);
					}
					
					Arrays.sort(featureNeigbors);
					for (int j = 0; j < featureNeigbors.length; j++) {
						System.out.print(featureNeigbors[j] + ", ");
					}
					System.out.println();

				// ----- 2 ---------------------------
					Arrays.fill(featureNeigbors, 0);
					i = 0;
					for (String feature : featureGraph.featureArray) {
						featureNeigbors[i++] = featureGraph.countNeighbors2(feature);
					}
	
					Arrays.sort(featureNeigbors);
					for (int j = 0; j < featureNeigbors.length; j++) {
						System.out.print(featureNeigbors[j] + ", ");
					}
					System.out.println();

				// ----- 3 ---------------------------
					Arrays.fill(featureNeigbors, 0);
					i = 0;
					for (String feature : featureGraph.featureArray) {
						featureNeigbors[i++] = featureGraph.countRealNeighbors(feature);
					}
	
					Arrays.sort(featureNeigbors);
					for (int j = 0; j < featureNeigbors.length; j++) {
						System.out.print(featureNeigbors[j] + ", ");
					}
					System.out.println();

				// ----- 3 ---------------------------
					Arrays.fill(featureNeigbors, 0);
					i = 0;
					for (String feature : featureGraph.featureArray) {
						featureNeigbors[i++] = featureGraph.countRealNeighbors2(feature);
					}
	
					Arrays.sort(featureNeigbors);
					for (int j = 0; j < featureNeigbors.length; j++) {
						System.out.print(featureNeigbors[j] + ", ");
					}
					System.out.println();
			}
			
			private void collectContainedFeatures(Node node, Set<String> featureNames) {
				if (node instanceof Literal) {
					featureNames.add((String) ((Literal)node).var);
				} else {
					for (Node child : node.getChildren()) {
						collectContainedFeatures(child, featureNames);
					}
				}
			}
			
			private void buildClique(Node... nodes) {
				final Set<String> featureNames = new HashSet<>();
				for (Node node : nodes) {
					collectContainedFeatures(node, featureNames);
				}
				for (Feature coreFeature : coreFeatures) {
					featureNames.remove(coreFeature.getName());
				}
				for (String featureName1 : featureNames) {
					for (String featureName2 : featureNames) {
						featureGraph.setEdge(featureName1, featureName2, FeatureGraph.EDGE_0q);
						featureGraph.setEdge(featureName1, featureName2, FeatureGraph.EDGE_1q);
					}
				}
			}
			
			private void imply(Literal implyNode, Literal impliedNode) {
				int negation = 0;
				if (!impliedNode.positive) {
					negation += 1;
				}
				if (!implyNode.positive) {
					negation += 2;
				}
				final String impliedFeatureName = (String) impliedNode.var;
				if (!coreFeatures.contains(getFeature(impliedFeatureName))) {
					featureGraph.implies((String) implyNode.var, impliedFeatureName, negation);
				}
			}
			
			private Collection<Node> simplify(Node node) {
				final Collection<Node> nodeList = new LinkedList<>();
				
				node = deMorgan(node);
				node = orToImply(node);
				node = elimnateNot(node);
				if (node instanceof And) {
					final Node[] children = node.getChildren();
					for (Node child : children) {
						nodeList.add(child);
					}
				} else {
					nodeList.add(node);
				}
				
				return nodeList;
			}
			
			private Node elimnateNot(Node node) {
				if (node instanceof Not) {
					Node child = node.getChildren()[0];
					if (child instanceof Literal) {
						((Literal) child).flip();
						return child;
					} else if (child instanceof Not) {
						return child.getChildren()[0];
					}
				}
				final Node[] children = node.getChildren();
				if (children != null) {
					for (int i = 0; i < children.length; i++) {
						children[i] = elimnateNot(children[i]);
					}
				}
				return node;
			}
			
			private Node deMorgan(Node node) {
				if (node instanceof Not) {
					Node child = node.getChildren()[0];
					if (child instanceof And) {
						final Node[] children = child.getChildren();
						final Node[] newChildren = new Node[children.length];
						for (int i = 0; i < children.length; i++) {
							newChildren[i] = new Not(children[i]);
						}
						node = new Or(newChildren);
					}
				}
				final Node[] children = node.getChildren();
				if (children != null) {
					for (int i = 0; i < children.length; i++) {
						children[i] = deMorgan(children[i]);
					}
				}
				return node;
			}
			
			private Node orToImply(Node node) {
				if (node instanceof Or && node.getChildren().length == 2) {
					final Node[] children = node.getChildren();
					node = new Implies(new Not(children[0]), children[1]);
				} else if (node instanceof And) {
					for (Node child : node.getChildren()) {
						orToImply(child);
					}
				}
				return node;
			}
			
			private void connect(Node constraintNode2) {
				//TODO simplify nodes: convert to implies, remove not node
				final Collection<Node> nodeList = simplify(constraintNode2);
				for (Node constraintNode : nodeList) {
					if (constraintNode instanceof Implies) {
						final Node leftNode = constraintNode.getChildren()[0];
						final Node rightNode = constraintNode.getChildren()[1];
						if (leftNode instanceof Literal) {
							final Literal implyNode = (Literal) leftNode;
							if (rightNode instanceof Literal) {
								imply(implyNode, (Literal) rightNode);
							} else if (rightNode instanceof And) {
								for (Node impliedNode : rightNode.getChildren()) {
									if (impliedNode instanceof Literal) {
										imply(implyNode, (Literal) impliedNode);
									} else {
										buildClique(implyNode, impliedNode);
									}
								}
							}
						} else if (leftNode instanceof Or) {
							if (rightNode instanceof Literal) {
								for (Node implyNode : leftNode.getChildren()) {
									if (implyNode instanceof Literal) {
										imply((Literal) implyNode, (Literal) rightNode);
									} else {
										buildClique(implyNode, rightNode);
									}
								}
							} else if (rightNode instanceof And) {
								for (Node implyNode : leftNode.getChildren()) {
									if (implyNode instanceof Literal) {
										for (Node impliedNode : rightNode.getChildren()) {
											if (impliedNode instanceof Literal) {
												imply((Literal) implyNode, (Literal) impliedNode);
											} else {
												buildClique(implyNode, impliedNode);
											}
										}
									} else {
										for (Node impliedNode : rightNode.getChildren()) {
											buildClique(implyNode, impliedNode);
										}
									}
								}
							}
						}
					} else {
						//TODO Implement other special cases
						buildClique(constraintNode);
					}
				}
			}
		};
		splittJob.schedule();
	}
	
	private static class DFSThreadPool {
		
		private static class DFSThread extends Thread {
			private final DFSThreadPool threadPool;
			
			public DFSThread(DFSThreadPool threadPool) {
				this.threadPool = threadPool;
			}

			@Override
			public void run() {
				final byte[] visited = new byte[threadPool.featureGraph.featureArray.length];
				for (String featureName = threadPool.featureNames.poll(); 
						featureName != null; featureName = threadPool.featureNames.poll()) {
					final int featureIndex = threadPool.featureGraph.featureMap.get(featureName);
					Arrays.fill(visited, (byte)0);
					threadPool.featureGraph.dfs(visited, featureIndex, true);
					Arrays.fill(visited, (byte)0);
					threadPool.featureGraph.dfs(visited, featureIndex, false);
					threadPool.worked();
				}
			}
			
		}
		
		private static final int NUMBER_OF_THREADS = 8;
		
		private final Thread[] threads = new Thread[NUMBER_OF_THREADS];
		
		private final ConcurrentLinkedQueue<String> featureNames;
		private final FeatureGraph featureGraph;
		private final WorkMonitor workMonitor;
		
		public DFSThreadPool(FeatureGraph featureGraph, Collection<String> featureNames, WorkMonitor workMonitor) {
			this.featureGraph = featureGraph;
			this.featureNames = new ConcurrentLinkedQueue<>(featureNames);
			this.workMonitor = workMonitor;
		}
		
		private synchronized void worked() {
			workMonitor.worked();
		}
		
		public void run() {
			for (int i = 0; i < NUMBER_OF_THREADS; i++) {
				final Thread thread = new DFSThread(this);
				threads[i] = thread;
				thread.start();
			}
			try {
				for (int i = 0; i < NUMBER_OF_THREADS; i++) {
					threads[i].join();
				}
			} catch (InterruptedException e) {
				FMCorePlugin.getDefault().logError(e);
			}
		}
	}
	
	private static class FeatureGraph {
		public static final byte
			EDGE_NONE = 0b00000000,
			EDGE_11 = 0b00000100, //0x04,
			EDGE_10 = 0b00001000, //0x08,
			EDGE_1q = 0b00001100, //0x0c,
			EDGE_01 = 0b00010000, //0x10,
			EDGE_00 = 0b00100000, //0x20,
			EDGE_0q = 0b00110000; //0x30;
		
		public static final byte
			MASK_1_11110011 = (byte) 0b11110011, //0xf3,
			MASK_0_11001111 = (byte) 0b11001111, //0xcf,
			MASK_1_00001100 = ~MASK_1_11110011,
			MASK_0_00110000 = ~MASK_0_11001111;
		
		public final String[] featureArray;
		
		private final byte[] adjMatrix;
		private final int size;
		private final HashMap<String, Integer> featureMap; 
		
		public FeatureGraph(Collection<Feature> features) {
			size = features.size();
			featureMap = new HashMap<>(size << 1);
			featureArray = new String[size];
			
			int i = 0;
			for (Feature feature : features) {
				featureArray[i++] = feature.getName();
			}
			Arrays.sort(featureArray);
			for (int j = 0; j < featureArray.length; j++) {
				featureMap.put(featureArray[j], j);
			}
			
			adjMatrix = new byte[size * size];
		}
		
		private void implies(String implyFeature, String impliedFeature) {
			implies(implyFeature, impliedFeature, 0);
		}
		
		private void implies(String implyFeature, String impliedFeature, int negation) {
			switch (negation) {
				case 0:
					setEdge(implyFeature, impliedFeature, FeatureGraph.EDGE_11);
					setEdge(impliedFeature, implyFeature, FeatureGraph.EDGE_00);
					break;
				case 1:
					setEdge(implyFeature, impliedFeature, FeatureGraph.EDGE_10);
					setEdge(impliedFeature, implyFeature, FeatureGraph.EDGE_10);
					break;
				case 2:
					setEdge(implyFeature, impliedFeature, FeatureGraph.EDGE_01);
					setEdge(impliedFeature, implyFeature, FeatureGraph.EDGE_01);
					break;
				case 3:
					setEdge(implyFeature, impliedFeature, FeatureGraph.EDGE_11);
					setEdge(impliedFeature, implyFeature, FeatureGraph.EDGE_00);
					break;
			}
		}

		public void setEdge(String from, String to, byte edgeType) {
			setEdge(featureMap.get(from), featureMap.get(to), edgeType);
		}
		
		public void setEdge(int from, int to, byte edgeType) {
			final int index = (from * size) + to;
			final byte oldValue;
			synchronized (adjMatrix) {
				oldValue = adjMatrix[index];
			}
			final int newValue;
			switch (edgeType) {
			case EDGE_NONE:
				newValue = EDGE_NONE;
				break;
			case EDGE_0q:
				switch (oldValue & MASK_0_00110000) {
				case EDGE_NONE:
					newValue = oldValue | edgeType | 2;
					break;
				default:
					newValue = oldValue;
				}
				break;
			case EDGE_00: case EDGE_01: 
				switch (oldValue & MASK_0_00110000) {
					case EDGE_NONE:
						newValue = oldValue | edgeType | 2;
						break;
					case EDGE_0q:
						newValue = (oldValue & MASK_0_11001111) | edgeType;
						break;
					default:
						newValue = oldValue | EDGE_0q;
				}
				break;
			case EDGE_1q:
				switch (oldValue & MASK_1_00001100) {
				case EDGE_NONE:
					newValue = oldValue | edgeType | 1;
					break;
				default:
					newValue = oldValue;
				}
				break;
			case EDGE_10: case EDGE_11: 
				switch (oldValue & MASK_1_00001100) {
					case EDGE_NONE:
						newValue = oldValue | edgeType | 1;
						break;
					case EDGE_1q:
						newValue = (oldValue & MASK_1_11110011) | edgeType;
						break;
					default:
						newValue = oldValue | EDGE_1q;
				}
				break;
			default:
				newValue = EDGE_NONE;
			}
			synchronized (adjMatrix) {
				adjMatrix[index] = (byte) newValue;
			}
		}
		
//		public byte getEdge(String from, String to) {
//			return getEdge(featureMap.get(from), featureMap.get(to));
//		}
		
		public byte getEdge(int fromIndex, int toIndex) {
			final int index = (fromIndex * size) + toIndex;
			return adjMatrix[index];
		}
		
		public void clearDiagonal() {
			for (int i = 0; i < adjMatrix.length; i+=(size + 1)) {
				adjMatrix[i] = EDGE_NONE;
			}
		}
		
		public int countNeighbors(String from) {
			final int fromIndex = featureMap.get(from);
			
			int count = 0;
			for (int i = (fromIndex * size), end = i + size; i < end; i++) {
				count += adjMatrix[i] % 2;
			}
			
			return count;
		}
		
		public int countRealNeighbors(String from) {
			final int fromIndex = featureMap.get(from);
			
			int count = 0;
			for (int i = (fromIndex * size), end = i + size; i < end; i++) {
				int edge = (adjMatrix[i] & MASK_1_00001100);
				if (edge == EDGE_10 || edge == EDGE_11) {
					count++;
				}
			}
			
			return count;
		}
		
		public int countRealNeighbors2(String from) {
			final int fromIndex = featureMap.get(from);
			
			int count = 0;
			for (int i = (fromIndex * size), end = i + size; i < end; i++) {
				int edge = (adjMatrix[i] & MASK_0_00110000);
				if (edge == EDGE_00 || edge == EDGE_01) {
					count++;
				}
			}
			
			return count;
		}
		
		public int countNeighbors2(String from) {
			final int fromIndex = featureMap.get(from);
			
			int count = 0;
			for (int i = (fromIndex * size), end = i + size; i < end; i++) {
				count += (adjMatrix[i] >>> 1) % 2;
			}
			
			return count;
		}
		
		// visited: 0 not visited, 1 visited (unknown status), 2 visited (known status)
		private void dfs(byte[] visited, int curFeature, boolean selected) {
			System.out.println(featureArray[curFeature] + " " + selected);
			visited[curFeature] = 2;
			
			for (int j = 0; j < visited.length; j++) {
				final byte visit = visited[j];
				if (visit < 2) {
					final byte childSelected;
					if (selected) {
						switch (getEdge(curFeature, j) & MASK_1_00001100) {
							case EDGE_10:
								// don't select child
								childSelected = 0;
								visited[j] = 2;
//								System.out.println("\tq " + featureArray[j]);
								break;
							case EDGE_11:
								// select child
								childSelected = 1;
								visited[j] = 2;
//								System.out.println("\tq " + featureArray[j]);
								break;
							case EDGE_1q:
								// ?
								if (visit == 1) {
									continue;
								}
								visited[j] = 1;
								childSelected = 2;
//								System.out.println("\tq " + featureArray[j]);
								break;
							default:
								continue;
						}
					} else {
						switch (getEdge(curFeature, j) & MASK_0_00110000) {
							case EDGE_00:
								// don't select child
								childSelected = 0;
								visited[j] = 2;
//								System.out.println("\t0 " + featureArray[j]);
								break;
							case EDGE_01:
								// select child
								childSelected = 1;
								visited[j] = 2;
//								System.out.println("\t1 " + featureArray[j]);
								break;
							case EDGE_0q:
								// ?
								if (visit == 1) {
									continue;
								}
								visited[j] = 1;
								childSelected = 2;
//								System.out.println("\tq " + featureArray[j]);
								break;
							default:
								continue;
						}
					}
					
					dfs_rec(visited, j, curFeature, childSelected, selected);
				}
			}
		}
		
		private void dfs_rec(byte[] visited, int curFeature, int parentFeature, byte selected, boolean parentSelected) {
			for (int j = 0; j < visited.length; j++) {
				final byte visit = visited[j];
				if (visit == 0) {
					final byte edge = getEdge(curFeature, j);
					switch (selected) {
						case 0:
							switch (edge & MASK_0_00110000) {
								// visit = 0, not selected, implies not selected
								case EDGE_00:
									visited[j] = 2;
//									System.out.println("\t0 " + featureArray[j]);
									setEdge(parentFeature, j, parentSelected ? EDGE_10 : EDGE_00);
									dfs_rec(visited, j, parentFeature, (byte)0, parentSelected);
									break;
								// visit = 0, not selected, implies selected
								case EDGE_01:
									visited[j] = 2;
//									System.out.println("\t1 " + featureArray[j]);
									setEdge(parentFeature, j, parentSelected ? EDGE_11 : EDGE_01);
									dfs_rec(visited, j, parentFeature, (byte)1, parentSelected);
									break;
								// visit = 0, not selected, implies ?
								case EDGE_0q:
									visited[j] = 1;
//									System.out.println("\tq " + featureArray[j]);
									setEdge(parentFeature, j, parentSelected ? EDGE_1q : EDGE_0q);
									dfs_rec(visited, j, parentFeature, (byte)2, parentSelected);
									break;
								// default ???
							}
							break;
						case 1:
							switch (edge & MASK_1_00001100) {
								// visit = 0, selected, implies not selected
								case EDGE_10:
									visited[j] = 2;
//									System.out.println("\t0 " + featureArray[j]);
									setEdge(parentFeature, j, parentSelected ? EDGE_10 : EDGE_00);
									dfs_rec(visited, j, parentFeature, (byte)0, parentSelected);
									break;
								// visit = 0, selected, implies selected
								case EDGE_11:
									visited[j] = 2;
//									System.out.println("\t1 " + featureArray[j]);
									setEdge(parentFeature, j, parentSelected ? EDGE_11 : EDGE_01);
									dfs_rec(visited, j, parentFeature, (byte)1, parentSelected);
									break;
								// visit = 0, selected, implies ?
								case EDGE_1q:
									visited[j] = 1;
//									System.out.println("\tq " + featureArray[j]);
									setEdge(parentFeature, j, parentSelected ? EDGE_1q : EDGE_0q);
									dfs_rec(visited, j, parentFeature, (byte)2, parentSelected);
									break;
								// default ???
							}
							break;
						case 2:
							if (edge > 0) {
								visited[j] = 1;
//								System.out.println("\tq " + featureArray[j]);
								setEdge(parentFeature, j, parentSelected ? EDGE_1q : EDGE_0q);
								dfs_rec(visited, j, parentFeature, (byte)2, parentSelected);
							}
							break;
					}
				} else if (visit == 1) {
					final byte edge = getEdge(curFeature, j);
					switch (selected) {
						case 0:
							switch (edge & MASK_0_00110000) {
								// visit = 1, not selected, implies not selected
								case EDGE_00:
									visited[j] = 2;
//									System.out.println("\t0 " + featureArray[j]);
									setEdge(parentFeature, j, parentSelected ? EDGE_10 : EDGE_00);
									dfs_rec(visited, j, parentFeature, (byte)0, parentSelected);
									break;
								// visit = 1, not selected, implies selected
								case EDGE_01:
									visited[j] = 2;
//									System.out.println("\t1 " + featureArray[j]);
									setEdge(parentFeature, j, parentSelected ? EDGE_11 : EDGE_01);
									dfs_rec(visited, j, parentFeature, (byte)1, parentSelected);
									break;
								// default ???
							}
							break;
						case 1:
							switch (edge & MASK_1_00001100) {
								// visit = 1, selected, implies not selected
								case EDGE_10:
									visited[j] = 2;
//									System.out.println("\t0 " + featureArray[j]);
									setEdge(parentFeature, j, parentSelected ? EDGE_10 : EDGE_00);
									dfs_rec(visited, j, parentFeature, (byte)0, parentSelected);
									break;
								// visit = 1, selected, implies selected
								case EDGE_11:
									visited[j] = 2;
//									System.out.println("\t1 " + featureArray[j]);
									setEdge(parentFeature, j, parentSelected ? EDGE_11 : EDGE_01);
									dfs_rec(visited, j, parentFeature, (byte)1, parentSelected);
									break;
								// default ???
							}
							break;
					}
				}
			}
		}
	}

}
