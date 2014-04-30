package de.ovgu.featureide.ui.statistics.core;

import java.util.HashMap;

import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.ui.statistics.core.composite.Parent;

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
	
	public static final String OPEN_FILE = "Please open a file from a FeatureIDE project";
	public static final String PRODUCT_LINE_IMPLEMENTATION = "Statistics of product-line implementation";
	public static final String CONTRACT_COMPLEXITY = "Statistics of product-line specification";
	public static final String VALID_CONFIGURATIONS = "Valid configurations of the feature model";
	public static final String NUMBER_OF_FEATURE = "Feature statistics";
	public static final String STATISTICS_OF_THE_FEATURE_MODEL = "Statistics of the feature model";
	public static final String PROJECT_NAME = "Project Name";

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
	
	public static final String NUMBER_PROJECT_METHOD_CONTRACT = "Number of method contracts in project";
	public static final String NUMBER_PROJECT_INVARIANT = "Number of class invariants in project";
	public static final String NUMBER_CLASS_METHOD_CONTRACT = "Number of classes with method contracts";
	public static final String NUMBER_CLASS_INVARIANT = "Number of classes with class invariants";
	public static final String NUMBER_METHOD_METHOD_CONTRACT = "Number of methods with method contracts";
	public static final String METHOD_CONTRACT_REFINEMENT = "Method contract refinements";
	public static final String METHOD_CONTRACTS_FEATURE = "Method contracts in features";
	
	public static final HashMap<String, String> REFINEMENT_COMPOSING_MECHANISM_MAPPING = new HashMap<String, String>(){
		private static final long serialVersionUID = 1L;

	{
        put("","No keyword");
        put("\\final_contract", "Plain Contracting");
        put("\\consecutive_contract", "Consecutive Contract");
        put("\\conjunctive_contract", "Conjunctive Contract");
        put("\\cumulative_contract", "Cumulative Contract");
        put("\\final_method", "Final Method");
    }};
	
}