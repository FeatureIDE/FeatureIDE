/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.fm.core.io;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileFilter;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Collection;

import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.Comparison;
import de.ovgu.featureide.fm.core.editing.ModelComparator;
import de.ovgu.featureide.fm.core.io.guidsl.GuidslReader;

/**
 * Basic test super-class for IFeatureModelReader/IFeatureModelWriter
 * implementations tests will write feature-models into a string and read it
 * back to check if the result is as expected
 * 
 * To add additional readers/writers extend this class and override abstract
 * methods
 * 
 * Add model.m files into folder testFeatureModels to add test cases
 * 
 * @author Fabian Benduhn
 */
@RunWith(Parameterized.class)
public abstract class TAbstractFeatureModelReaderWriter {

	// featuremodels are created by using GuidslWriter, so for each test case
	// there should be an corresponding test case for the
	// GuidslReader which tests the resulting FeatureModel directly

	// TODO replace MODEL_FILE_PATH by something that works on both: build-server and offline in
	// workspace
	// For now: uncomment this to run tests in workspace:
//	protected static String sep = System.getProperty("file.separator");
//	protected static File MODEL_FILE_PATH = new File("src" + sep
//			+ "testFeatureModels" + sep);
	 protected static File MODEL_FILE_PATH = new
	 File("/vol1/teamcity_itidb/TeamCity/buildAgent/work/featureide/tests/de.ovgu.featureide.fm.core-test/src/testFeatureModels/");

	IFeatureModelWriter writer;
	IFeatureModelReader reader;
	FeatureModel fm;
	File file;

	public TAbstractFeatureModelReaderWriter(File file) {
		this.file = file;
	}

	@Before
	public void setUpEachTest() {
		if (fm == null)
			fm = new FeatureModel();
		else
			fm.reset();
		writer = getWriter(fm);
		reader = getReader(fm);
	}
	

	@Parameters
	public static Collection<File[]> getFiles() {
		Collection<File[]> params = new ArrayList<File[]>();
		for (File f : MODEL_FILE_PATH.listFiles(getFileFilter(".m"))) {
			File[] file = new File[1];
			file[0] = f;
			params.add(file);
		}
		System.out.println(params);
		return params;
	}

	@Test
	public void testModel() throws FileNotFoundException,
			UnsupportedModelException {

		assertTrue("Test for following model failed: " + file.getName()+"\n", testFromFile(file));
	}

	/**
	 * returns a FileFilter which accepts filenames ending with s;
	 */
	private final static FileFilter getFileFilter(final String s) {
		FileFilter filter = new FileFilter() {

			@Override
			public boolean accept(File pathname) {
				System.out.println("accept" + pathname);
				if (pathname.getName().endsWith(s)) {
					System.out.println("true");
					return true;
				} else {
					System.out.println("false");
					return false;
				}
			}
		};
		return filter;
	}

	/**
	 * @param guidslReader
	 *            *
	 * @throws FileNotFoundException
	 * */
	private final boolean testFromFile(File file) throws FileNotFoundException {
		FeatureModel fmOld = fm;
		GuidslReader guidslReader = new GuidslReader(fm);
		try {
			guidslReader.readFromFile(file);

			writeAndReadModel();
		} catch (UnsupportedModelException e) {
			assertFalse(e.getMessage(), true);
		}
		return compareModels(fmOld, fm);
	}

	/**
	 * TODO: Replace by a check for direct equality, i.e oldfm.equals(newfm)
	 * 
	 */
	private boolean compareModels(FeatureModel oldfm, FeatureModel newfm) {
		ModelComparator mc = new ModelComparator(10000);
		return (mc.compare(oldfm, newfm).equals(Comparison.REFACTORING));
	}

	public final void writeAndReadModel() throws UnsupportedModelException {

		String s = writer.writeToString();

		reader.readFromString(s);

	}

	protected abstract IFeatureModelWriter getWriter(FeatureModel fm);

	protected abstract IFeatureModelReader getReader(FeatureModel fm);

}
