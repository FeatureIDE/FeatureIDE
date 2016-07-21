/*******************************************************************************
 * Copyright (c) 2013 University of Bergamo - Italy
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 * 
 * Contributors:
 *   Paolo Vavassori - initial API and implementation
 *   Angelo Gargantini - utils and architecture
 ******************************************************************************/
package de.ovgu.featureide.fm.core.io.sxfm;

import java.io.File;
import java.io.FilenameFilter;
import java.util.ArrayList;
import java.util.Collection;

import org.junit.Assert;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
//import org.junit.runner.RunWith;
//import org.junit.runners.Parameterized;
//import org.junit.runners.Parameterized.Parameters;

/**
 * convert all the splot models using the double conversion of FeatureIDE (read an write).
 * All the resulting models will be read by FeatureIDE
 * 
 * 
 * @author garganti
 * 
 */
// TODO currently splot models support different attributes then featureIDE model.
// 		replace System.err.println by assertions if a correct conversion is possible. 
//@RunWith(Parameterized.class)
public class Experiment_ConvertSPLOTmodels extends Experiment_SPLOTmodels{
	protected static File MODEL_FILE_FOLDER = new
			 File("/home/itidbrun/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.fm.core-test/src/splotmodels/");
	private static File DESTINATION = new
			 File("/home/itidbrun/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.fm.core-test/src/splotmodels_new/");
	
	private File modelFile;

	public Experiment_ConvertSPLOTmodels(File modelFile) {
		this.modelFile = modelFile;
	}
	
//	@Parameters
	public static Collection<Object[]> getModels() {
		if (!MODEL_FILE_FOLDER.canRead()){
			MODEL_FILE_FOLDER = new File(ClassLoader.getSystemResource("splotmodels").getPath());
		}
		if (!DESTINATION.canRead()){
			DESTINATION = new File(ClassLoader.getSystemResource("splotmodels_new").getPath());
		}
		
		Assert.assertTrue(MODEL_FILE_FOLDER.isDirectory());
		File[] children = MODEL_FILE_FOLDER.listFiles(new FilenameFilter() {

			@Override
			public boolean accept(File dir, String name) {
				return name.endsWith(".xml");
			}
		});
		Collection<Object[]> params = new ArrayList<Object[]>();
		for (File f : children) {
			params.add(new Object[]{f});
		}
		return params;
	}

	/**
	 * Tests if conversion is equivalent.
	 * @throws Exception
	 */
//	@Test
	public void convertSPLOTmodel()
			throws Exception {
		String origin = modelFile.getAbsolutePath();
		
		// preconditions
		File modelFileOrigin = new File(origin);
		assert modelFileOrigin.exists() && modelFileOrigin.isFile();
		assert DESTINATION.isDirectory();
		
		//
		// read the same SPLOT file using the FeatureiDE reader
		IFeatureModel fm_original = FMFactoryManager.getFactory().createFeatureModel();		
		SXFMFormat format = new SXFMFormat();
		final ProblemList problems = FileHandler.load(modelFileOrigin.toPath(), fm_original, format);
		if (problems.containsError()) {
			System.err.println("SKIPPING " + modelFile + " cause :" + problems.getErrors().toString());
		}
		// save with the same name in the other directory (same format sxfm)
		// using the featureidewriter
		String newPath = DESTINATION + File.separator + modelFileOrigin.getName();
		File newFile = new File(newPath);
		

		if (FileHandler.save(newFile.toPath(), fm_original, format).containsError()) {
			newFile.delete();
		} else {
			// perform the analysis using the SPLAR reader and analyzer
			// take the two models 
			splar.core.fm.FeatureModel originalSplotModel = getSplotModel(origin);
			splar.core.fm.FeatureModel newSplotModel = getSplotModel(newPath);
			// number of nodes (should be the same)
			int nNodes = originalSplotModel.getNodes().size();
			int nNodesP = newSplotModel.getNodes().size();	
			if (nNodes !=  nNodesP) {
				System.err.println("Nodes are not equivalent @ "+ modelFile + " " + nNodes + " : " +  nNodesP);
				return;
			}
			// number of valid products
			long splotModelNproducts = getNumberOfValidProducts(originalSplotModel);
			long splotModelNproductsP = getNumberOfValidProducts(newSplotModel);
			if (splotModelNproducts !=  splotModelNproductsP) {
				System.err.println("Number of products are not equivalent @ "+ modelFile + " " + splotModelNproducts + " : " +  splotModelNproductsP);
			}
		}
	}

}
