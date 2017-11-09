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
package de.ovgu.featureide.core.featuremodeling;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.ovgu.featureide.fm.core.FMComposerExtension;
import de.ovgu.featureide.fm.core.IFMComposerExtension;

/**
 * Test class for the {@link FMComposerExtension}.
 *
 * @author Florian Proksch
 */
public class TFeatureModelingFMExtension {

	private static FeatureModelingFMExtension f1 = new FeatureModelingFMExtension();
	private static IFMComposerExtension f2 = new FMComposerExtension();
	static {
		f1.hasComposer(false);
		f2.hasComposer(true);
	}

	@Test
	public void FM_valid() {
		assertTrue(f1.isValidFeatureName("Hans Christian Andersen"));
	}

	@Test
	public void FM_valid2() {
		assertTrue(f1.isValidFeatureName("% a9 0km !�nc"));
	}

	@Test
	public void FM_valid3() {
		assertFalse(f1.isValidFeatureName(" Han\"s Christian Andersen"));
	}

	@Test
	public void FM_valid4() {
		assertTrue(f1.isValidFeatureName("Hans and Christian Andersen"));
	}

	@Test
	public void FM_valid5() {
		assertTrue(f1.isValidFeatureName("Hans or Christian Andersen"));
	}

	@Test
	public void FM_valid6() {
		assertTrue(f1.isValidFeatureName("Hans iff Christian Andersen"));
	}

	@Test
	public void FM_valid7() {
		assertTrue(f1.isValidFeatureName("Hans implies Christian Andersen"));
	}

	@Test
	public void notFM_valid() {
		assertTrue(f2.isValidFeatureName("HansChristianAndersen"));
	}

	@Test
	public void notFM_valid2() {
		assertTrue(f2.isValidFeatureName("Javaidentifier"));
	}

	@Test
	public void FM_notvalid1() {
		assertFalse(f1.isValidFeatureName(" Han(s Christian Andersen"));
	}

	@Test
	public void FM_notvalid2() {
		assertFalse(f1.isValidFeatureName(" Han)s Christian Andersen"));
	}

	@Test
	public void notFM_notvalid() {
		assertFalse(f2.isValidFeatureName("Christian Andersen"));
	}

	@Test
	public void notFM_notvalid2() {
		assertFalse(f2.isValidFeatureName("\" n"));
	}

}
