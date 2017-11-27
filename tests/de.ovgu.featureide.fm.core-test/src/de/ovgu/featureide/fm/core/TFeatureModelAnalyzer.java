/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.FileFilter;
import java.util.Map;

import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties;
import de.ovgu.featureide.fm.core.analysis.ConstraintProperties.ConstraintStatus;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties;
import de.ovgu.featureide.fm.core.analysis.FeatureProperties.FeatureStatus;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;

/**
 * Tests for {@link FeatureModelAnalyzer}
 *
 * @author Jens Meinicke
 * @author Stefan Krueger
 * @author Florian Proksch
 */
public class TFeatureModelAnalyzer {

	protected static File MODEL_FILE_FOLDER = Commons.getRemoteOrLocalFolder("analyzefeaturemodels/");

	private static final FileFilter filter = new FileFilter() {

		@Override
		public boolean accept(File pathname) {
			return pathname.getName().endsWith(".xml");
		}
	};

	private static IFeatureModel FM_test_1 = init("test_1.xml");
	private static IFeature FM1_F1 = FM_test_1.getFeature("F1");
	private static IFeature FM1_F2 = FM_test_1.getFeature("F2");
	private static IConstraint FM1_C1 = FM_test_1.getConstraints().get(0);
	private static Map<IFeatureModelElement, Object> FM1_DATA = FeatureModelManager.getAnalyzer(FM_test_1).analyzeFeatureModel(null);

	private static IFeatureModel FM_test_2 = init("test_2.xml");
	private static IFeature FM2_F1 = FM_test_2.getFeature("F1");
	private static IFeature FM2_F2 = FM_test_2.getFeature("F2");
	private static IFeature FM2_F3 = FM_test_2.getFeature("F3");
	private static IConstraint FM2_C1 = FM_test_2.getConstraints().get(0);
	private static IConstraint FM2_C2 = FM_test_2.getConstraints().get(1);
	private static IConstraint FM2_C3 = FM_test_2.getConstraints().get(2);
	private static Map<IFeatureModelElement, Object> FM2_DATA = FeatureModelManager.getAnalyzer(FM_test_2).analyzeFeatureModel(null);

	private static IFeatureModel FM_test_3 = init("test_3.xml");
	private static IFeature FM3_F2 = FM_test_3.getFeature("F2");
	private static IFeature FM3_F3 = FM_test_3.getFeature("F3");
	private static IConstraint FM3_C1 = FM_test_3.getConstraints().get(0);
	private static Map<IFeatureModelElement, Object> FM3_DATA = FeatureModelManager.getAnalyzer(FM_test_3).analyzeFeatureModel(null);

	private static IFeatureModel FM_test_4 = init("test_4.xml");
	private static IFeature FM4_F1 = FM_test_4.getFeature("I");
	private static IFeature FM4_F2 = FM_test_4.getFeature("D");
	private static IFeature FM4_F3 = FM_test_4.getFeature("E");
	private static IFeature FM4_F4 = FM_test_4.getFeature("K");
	private static IFeature FM4_F5 = FM_test_4.getFeature("L");
	private static IFeature FM4_F6 = FM_test_4.getFeature("N");
	private static IFeature FM4_F7 = FM_test_4.getFeature("P");
	private static IFeature FM4_F8 = FM_test_4.getFeature("M");
	private static IFeature FM4_F9 = FM_test_4.getFeature("C");
	private static IFeature FM4_F10 = FM_test_4.getFeature("J");
	private static Map<IFeatureModelElement, Object> FM4_DATA = FeatureModelManager.getAnalyzer(FM_test_4).analyzeFeatureModel(null);

	private static IFeatureModel FM_test_7 = init("test_7.xml");
	private static IFeature FM7_F1 = FM_test_7.getFeature("H");
	private static IConstraint FM7_C1 = FM_test_7.getConstraints().get(0);
	private static Map<IFeatureModelElement, Object> FM7_DATA = FeatureModelManager.getAnalyzer(FM_test_7).analyzeFeatureModel(null);

	private static IFeatureModel FM_test_8 = init("test_8.xml");
	private static IFeature FM8_F1 = FM_test_8.getFeature("B");
	private static IFeature FM8_F2 = FM_test_8.getFeature("C");
	private static Map<IFeatureModelElement, Object> FM8_DATA = FeatureModelManager.getAnalyzer(FM_test_8).analyzeFeatureModel(null);

	private static final IFeatureModel init(String name) {
		IFeatureModel fm = null;
		for (final File f : MODEL_FILE_FOLDER.listFiles(filter)) {
			if (f.getName().equals(name)) {
				fm = FeatureModelManager.load(f.toPath());
				if (fm != null) {
					break;
				}
			}
		}
		return fm;
	}

	@Test
	public void TFalseOptional_FM1_F1() {
		assertTrue(((FeatureProperties) FM1_DATA.get(FM1_F1)).hasStatus(FeatureStatus.FALSE_OPTIONAL));
	}

	@Test
	public void TFalseOptional_FM1_F2() {
		assertTrue(((FeatureProperties) FM1_DATA.get(FM1_F2)).hasStatus(FeatureStatus.FALSE_OPTIONAL));
	}

	@Test
	public void TFalseOptional_FM1_C1() {
		assertFalse(((ConstraintProperties) FM1_DATA.get(FM1_C1)).getFalseOptionalFeatures().isEmpty());
	}

	@Test
	public void TFalseOptional_FM1_C1_F1() {
		assertTrue(((ConstraintProperties) FM1_DATA.get(FM1_C1)).getFalseOptionalFeatures().contains(FM1_F1));
	}

	@Test
	public void TFalseOptional_FM1_C1_F2() {
		assertTrue(((ConstraintProperties) FM1_DATA.get(FM1_C1)).getFalseOptionalFeatures().contains(FM1_F2));
	}

	@Test
	public void TFalseOptional_FM2_F1() {
		assertTrue(((FeatureProperties) FM2_DATA.get(FM2_F1)).hasStatus(FeatureStatus.FALSE_OPTIONAL));
	}

	@Test
	public void TFalseOptional_FM2_F2() {
		assertTrue(((FeatureProperties) FM2_DATA.get(FM2_F2)).hasStatus(FeatureStatus.FALSE_OPTIONAL));
	}

	@Test
	public void TFalseOptional_FM2_F3() {
		assertTrue(((FeatureProperties) FM2_DATA.get(FM2_F3)).hasStatus(FeatureStatus.OPTIONAL));
	}

	@Test
	public void TFalseOptional_FM2_C1() {
		assertFalse(((ConstraintProperties) FM2_DATA.get(FM2_C1)).getFalseOptionalFeatures().isEmpty());
	}

	@Test
	public void TFalseOptional_FM2_C1_F1() {
		assertTrue(((ConstraintProperties) FM2_DATA.get(FM2_C1)).getFalseOptionalFeatures().contains(FM2_F1));
	}

	@Test
	public void TFalseOptional_FM2_C1_F2() {
		assertTrue(((ConstraintProperties) FM2_DATA.get(FM2_C1)).getFalseOptionalFeatures().contains(FM2_F2));
	}

	@Test
	public void TFalseOptional_FM2_C1_F3() {
		assertFalse(((ConstraintProperties) FM2_DATA.get(FM2_C1)).getFalseOptionalFeatures().contains(FM2_F3));
	}

	@Test
	public void TFalseOptional_FM2_C2() {
		assertTrue(((ConstraintProperties) FM2_DATA.get(FM2_C2)).hasStatus(ConstraintStatus.REDUNDANT));
	}

	@Test
	public void TFalseOptional_FM2_C2_F() {
		assertTrue(((ConstraintProperties) FM2_DATA.get(FM2_C2)).getFalseOptionalFeatures().isEmpty());
	}

	@Test
	public void TFalseOptional_FM2_C3() {
		assertTrue(((ConstraintProperties) FM2_DATA.get(FM2_C3)).hasStatus(ConstraintStatus.REDUNDANT));
	}

	@Test
	public void TFalseOptional_FM2_C3_F() {
		assertTrue(((ConstraintProperties) FM2_DATA.get(FM2_C3)).getFalseOptionalFeatures().isEmpty());
	}

	@Test
	public void TFalseOptional_FM3_F2() {
		assertTrue(((FeatureProperties) FM3_DATA.get(FM3_F2)).hasStatus(FeatureStatus.FALSE_OPTIONAL));
	}

	@Test
	public void TDead_FM3_F2() {
		assertTrue(((FeatureProperties) FM3_DATA.get(FM3_F3)).hasStatus(FeatureStatus.DEAD));
	}

	@Test
	public void TFalseOptional_FM3_C1() {
		assertFalse(((ConstraintProperties) FM3_DATA.get(FM3_C1)).getDeadFeatures().isEmpty());
	}

	@Test
	public void TFalseOptional_FM3_C1_contains() {
		assertTrue(((ConstraintProperties) FM3_DATA.get(FM3_C1)).getFalseOptionalFeatures().contains(FM3_F2));
	}

	@Test
	public void TDead_FM3_C1_contains() {
		assertTrue(((ConstraintProperties) FM3_DATA.get(FM3_C1)).getDeadFeatures().contains(FM3_F3));
	}

	@Test
	public void TFalseOptional_FM4_F1() {
		assertTrue(((FeatureProperties) FM4_DATA.get(FM4_F10)).hasStatus(FeatureStatus.FALSE_OPTIONAL));
	}

	@Test
	public void TFalseOptional_FM7_F1() {
		assertTrue(((FeatureProperties) FM7_DATA.get(FM7_F1)).hasStatus(FeatureStatus.FALSE_OPTIONAL));
	}

	@Test
	public void TRedundantConstr_FM7_C1() {
		assertTrue(((ConstraintProperties) FM7_DATA.get(FM7_C1)).hasStatus(ConstraintStatus.REDUNDANT));
	}

	@Test
	public void TDead_FM8_F1() {
		assertTrue(((FeatureProperties) FM8_DATA.get(FM8_F1)).hasStatus(FeatureStatus.DEAD));
	}

	@Test
	public void TDead_FM8_F2() {
		assertTrue(((FeatureProperties) FM8_DATA.get(FM8_F2)).hasStatus(FeatureStatus.DEAD));
	}

	@Test
	public void TIndeterminate_Hidden_FM1_F0() {
		assertFalse(((FeatureProperties) FM4_DATA.get(FM4_F2)).hasStatus(FeatureStatus.INDETERMINATE_HIDDEN));
	}

	@Test
	public void TIndeterminate_Hidden_FM1_F1() {
		assertTrue(((FeatureProperties) FM4_DATA.get(FM4_F3)).hasStatus(FeatureStatus.INDETERMINATE_HIDDEN));
	}

	@Test
	public void TIndeterminate_Hidden_FM1_F2() {
		assertFalse(((FeatureProperties) FM4_DATA.get(FM4_F4)).hasStatus(FeatureStatus.INDETERMINATE_HIDDEN));
	}

	@Test
	public void TIndeterminate_Hidden_FM1_F3() {
		assertFalse(((FeatureProperties) FM4_DATA.get(FM4_F5)).hasStatus(FeatureStatus.INDETERMINATE_HIDDEN));
	}

	@Test
	public void TIndeterminate_Hidden_FM1_F4() {
		assertTrue(((FeatureProperties) FM4_DATA.get(FM4_F6)).hasStatus(FeatureStatus.INDETERMINATE_HIDDEN));
	}

	@Test
	public void TIndeterminate_Hidden_FM1_F5() {
		assertTrue(((FeatureProperties) FM4_DATA.get(FM4_F7)).hasStatus(FeatureStatus.INDETERMINATE_HIDDEN));
	}

	@Test
	public void TIndeterminate_Hidden_FM1_F6() {
		assertFalse(((FeatureProperties) FM4_DATA.get(FM4_F8)).hasStatus(FeatureStatus.INDETERMINATE_HIDDEN));
	}

	@Test
	public void TIndeterminate_Hidden_FM1_F7() {
		assertFalse(((FeatureProperties) FM4_DATA.get(FM4_F9)).hasStatus(FeatureStatus.INDETERMINATE_HIDDEN));
	}

	@Test
	public void TIndeterminate_Hidden_FM1_F8() {
		assertTrue(((FeatureProperties) FM4_DATA.get(FM4_F1)).hasStatus(FeatureStatus.INDETERMINATE_HIDDEN));
	}

}
