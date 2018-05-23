/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
