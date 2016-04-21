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
package de.ovgu.contracts.builder;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.LinkedList;
import java.util.List;

import composer.CmdLineInterpreter;
import composer.CompositionException;
import composer.FSTGenComposerExtension;
import composer.ICompositionErrorListener;

import de.ovgu.cide.fstgen.ast.FSTTerminal;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.meta.featuremodel.FeatureModelClassGenerator;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * Builds the metaproduct. Clone of FeatureHouseFomposer.
 * @author Jens Meinicke
 *
 */
public class FeatureHouseBuilder {
	private static final String CONTRACT_COMPOSITION_EXPLICIT_CONTRACTING = "explicit_contracting";
	
	private ICompositionErrorListener compositionErrorListener = createCompositionErrorListener();

	private ICompositionErrorListener createCompositionErrorListener() {
		return new ICompositionErrorListener() {

			@Override
			public void parseErrorOccured(final CompositionException e) {
				FSTTerminal terminal = e.getTerminalB();
				
				if (e.getMessage().contains("\\original")) {
					if (!e.getTerminalB().getBody().contains("\\original")) {
						terminal = e.getTerminalA();
					}
				}

				int lineFile = -1;
				if (terminal != null) {
					lineFile = terminal.beginLine;
					System.out.println("Composition error occured: " + lineFile + " @ " + terminal.getName());
				}
			}

		};
	}
	
	private String configFolder;
	private String featureFolder;
	private String sourceFolder;
	private String featureModelPath;

	public FeatureHouseBuilder(final String featureFolder, final String configFolder, 
	        final String featureModelPath, final String sourceFolder) {
		this.configFolder = configFolder;
		this.featureFolder = featureFolder;
		this.sourceFolder = sourceFolder;
		this.featureModelPath = featureModelPath;
	}
	
	public final void build(final String type) {
		buildMetaProduct(configFolder, featureFolder, sourceFolder, featureModelPath, type);
	}
	
	private void buildMetaProduct(final String configPath,
			final String featurePath, final String sourcePath, final String featureModelPath, final String type) {
		new FeatureModelClassGenerator(new File(featureModelPath), sourcePath, type);
		FSTGenComposerExtension.key = IFeatureProject.META_THEOREM_PROVING.equals(type) || IFeatureProject.META_MODEL_CHECKING_BDD_JAVA_JML.equals(type);
		FSTGenComposerExtension composer = new FSTGenComposerExtension();
		composer.addCompositionErrorListener(compositionErrorListener);
		FeatureModel featureModel = new FeatureModel();
		try {
			new XmlFeatureModelReader(featureModel).readFromFile(new File(featureModelPath));
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (UnsupportedModelException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		List<String> featureOrderList = featureModel.getConcreteFeatureNames();
		// dead features should not be composed
		LinkedList<String> deadFeatures = new LinkedList<String>();
		for (Feature deadFeature : featureModel.getAnalyser().getDeadFeatures()) {
			deadFeatures.add(deadFeature.getName());
		}
		
		String[] features = new String[featureOrderList.size()];
		int i = 0;		
		for (String f : featureOrderList) {
			if (!deadFeatures.contains(f)) {
				features[i++] = f;
			}
		}
		
		try {
			composer.buildMetaProduct(
					getArguments(configPath, featurePath, sourcePath, CONTRACT_COMPOSITION_EXPLICIT_CONTRACTING)
					, features);
		} catch (Error e) {
			e.printStackTrace();
		}
	}
	
	private String[] getArguments(final String configPath,
			final String basePath, final String outputPath, final String contract) {
		return new String[] {
				CmdLineInterpreter.INPUT_OPTION_EQUATIONFILE, configPath,
				CmdLineInterpreter.INPUT_OPTION_BASE_DIRECTORY, basePath,
				CmdLineInterpreter.INPUT_OPTION_OUTPUT_DIRECTORY, outputPath + "/",
				CmdLineInterpreter.INPUT_OPTION_CONTRACT_STYLE, contract
		};
	}
}

