/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.featurehouse.refactoring;

import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.junit.Test;

import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
public class RenameClassRefactoringTest extends RenameRefactoringTest {

	@Test
	public void testRenameClass() throws Exception {
		final RefactoringStatus status = new RefactoringStatus();
		Set<Integer> changedHashCodes = hashCodeOfChanges(".Main", "RenamedMain", status);
		Set<Integer> expectedHashCodes = getExpectedHashCodeVirtualMethod();
		assertTrue(changedHashCodes.size() == expectedHashCodes.size());
		assertTrue(changedHashCodes.containsAll(expectedHashCodes));
	}

	@Test
	public void testRenameClassExisting() throws Exception {
		final RefactoringStatus status = new RefactoringStatus();
		Set<Integer> changedHashCodes = hashCodeOfChanges(".Main", "SubMain", status);
		assertTrue(status.hasError());
		assertTrue(changedHashCodes.size() == 0);
	}

	private Set<Integer> getExpectedHashCodeVirtualMethod() throws CoreException, IOException {
		final Set<Integer> expectedHashCode = new HashSet<Integer>();
		IFile file = featureProject.getProject().getFile("features_expected/testRenameClass/Beautiful/RenamedMain.java");
		expectedHashCode.add(getHashCodeOfFile(file));
		file = featureProject.getProject().getFile("features_expected/testRenameClass/Hello/RenamedMain.java");
		expectedHashCode.add(getHashCodeOfFile(file));
		file = featureProject.getProject().getFile("features_expected/testRenameClass/Hello/SubMain.java");
		expectedHashCode.add(getHashCodeOfFile(file));
		file = featureProject.getProject().getFile("features_expected/testRenameClass/Wonderful/RenamedMain.java");
		expectedHashCode.add(getHashCodeOfFile(file));
		file = featureProject.getProject().getFile("features_expected/testRenameClass/World/RenamedMain.java");
		expectedHashCode.add(getHashCodeOfFile(file));
		return expectedHashCode;
	}

	@Override
	protected boolean hasSameType(AbstractSignature signature) {
		return (signature instanceof FujiClassSignature);
	}

	@Override
	protected RenameRefactoring<?> getRefactoring(String fullSigName) {
		FujiClassSignature clazz = (FujiClassSignature) getNamedSignature(fullSigName);
		return new RenameTypeRefactoring(clazz, featureProject, null);
	}

}
