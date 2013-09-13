package de.ovgu.featureide.ui.statistics.core.composite;

import org.eclipse.jface.viewers.TreeViewer;

/**
 * Defines descriptions for nodes in the TreeViewer in order to keep everything
 * in one place.
 * 
 * @see Parent
 * @see TreeViewer
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public interface StatisticsIds {
	
	public static final String SEPARATOR = ": ";
	public static final String NUMBER_FEATURES = "Number of features";
	public static final String NUMBER_CONCRETE = "Number of concrete features";
	public static final String NUMBER_ABSTRACT = "Number of abstract features";
	public static final String NUMBER_TERMINAL = "Number of terminal features";
	public static final String NUMBER_COMPOUND = "Number of compound features";
	public static final String NUMBER_HIDDEN = "Number of hidden features";
	public static final String NUMBER_CONSTRAINTS = "Number of constraints";
	public static final String MODEL_VOID = "Feature model is valid (not void)";
	public static final String MODEL_TIMEOUT = MODEL_VOID + "timeout";
	public static final String DESC_COMPOSER_NAME = "Generation Tool";
	public static final String DESC_CONFIGS = "Number of configurations";
	public static final String DESC_VARIANTS = "Number of program variants";
	public static final String DESC_FEATURE_COMPLEXITY = "Feature - Details";
	public static final String NUMBER_ROLE = "Number of roles";
	public static final String NUMBER_CLASS = "Number of classes";
	public static final String NUMBER_METHOD = "Number of methods";
	public static final String NUMBER_FIELD = "Number of fields";
	public static final String NUMBER_METHOD_U = "Number of unique methods";
	public static final String NUMBER_FIELD_U = "Number of unique fields";
}