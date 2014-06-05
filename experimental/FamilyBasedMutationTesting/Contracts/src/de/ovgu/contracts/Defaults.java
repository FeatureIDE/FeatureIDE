package de.ovgu.contracts;

/**
 * Contains default paths and paramters.
 * @author Jens Meinicke
 *
 */
public interface Defaults {
    enum MutationType {
	        ALL, JML_ONLY, JAVA_ONLY
    }
	String TYPE_JAVA = "type:Java";
	String TYPE_JML = "type:JML";
	String TYPE_ALL = "type:ALL";
    int ANALYSIS_ROUNDS = 1;

    int MUTATION_CASE_AMOUNT = 20;

    String WORKSPACE_PATH = "";//TODO set path to your workspace

//    String MAIN_CLASS = "StringMatcher";
//    String PROJECT_NAME = "StringMatcher-FH-JML";
    String MAIN_CLASS = "Main";
    String PROJECT_NAME = "BankAccount-FH-JML_new";
    String CASE_STUDY_PATH = WORKSPACE_PATH + PROJECT_NAME + "\\";
    String FEATURE_PATH = CASE_STUDY_PATH + "features\\";

//    String CONFIG_PATH = CASE_STUDY_PATH + "configs\\equals.config";
    String CONFIG_PATH = CASE_STUDY_PATH + "configs\\default.config";
//    String FEATUREMODEL_PATH = CASE_STUDY_PATH + "model.xml";


    String CONTRACTS_PATH = WORKSPACE_PATH + "Contracts\\";
    String JML = CONTRACTS_PATH + "lib\\jml\\jmlruntime.jar ";
    String LIB_PATH = CONTRACTS_PATH + "lib\\";
    String TMP_PATH = CONTRACTS_PATH + "tmp\\";
    String NEW_FEATURE_PATH = TMP_PATH + "features\\";
    String BIN_PATH = TMP_PATH + "build\\bin\\";
    String SRC_PATH = TMP_PATH + "build\\src\\";
    String FM_PATH = SRC_PATH + "defailt";
    String RESULTS_PATH = CONTRACTS_PATH + "results\\";

    String JPF = "projects\\jpf\\jpf-core\\build\\";// TODO set path to your jpf build

}
