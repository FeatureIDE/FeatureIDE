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
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;

/**
 * TODO description
 * 
 * @author Steffen Schulze
 */
public class RenameMethodRefactoringTest extends RenameRefactoringTest {

	@Test
	public void testRenameVirtualMethod() throws Exception {
		final RefactoringStatus status = new RefactoringStatus();
		Set<Integer> changedHashCodes = hashCodeOfChanges(".Main.print", "println", status);
		Set<Integer> expectedHashCodes = getExpectedHashCodeVirtualMethod();
		assertTrue(status.isOK());
		assertTrue(changedHashCodes.size() == expectedHashCodes.size());
		assertTrue(changedHashCodes.containsAll(expectedHashCodes));
	}

	@Test
	public void testRenameVirtualMethodInPackage() throws Exception {
		final RefactoringStatus status = new RefactoringStatus();
		Set<Integer> changedHashCodes = hashCodeOfChanges("ovgu.SubMain.print", "println", status);
		Set<Integer> expectedHashCodes = getExpectedHashCodeVirtualMethodInPackage();
		assertTrue(status.isOK());
		assertTrue(changedHashCodes.size() == expectedHashCodes.size());
		assertTrue(changedHashCodes.containsAll(expectedHashCodes));
	}

	@Test
	public void testStaticMethod() throws Exception {
		final RefactoringStatus status = new RefactoringStatus();
		Set<Integer> changedHashCodes = hashCodeOfChanges(".Main.main", "mainStatic", status);
		Set<Integer> expectedHashCodes = getExpectedHashCodeStaticMethod();
		assertTrue(status.isOK());
		assertTrue(changedHashCodes.size() == expectedHashCodes.size());
		assertTrue(changedHashCodes.containsAll(expectedHashCodes));
	}

	@Test
	public void testExistingMethod() throws Exception {
		final RefactoringStatus status = new RefactoringStatus();
		Set<Integer> changedHashCodes = hashCodeOfChanges(".Main.print", "print1", status);
		assertTrue(status.hasError());
		assertTrue(changedHashCodes.size() == 0);
	}

	private Set<Integer> getExpectedHashCodeStaticMethod() throws CoreException, IOException {
		final IFile file = featureProject.getProject().getFile("features_expected/testRenameStaticMethod/Hello/Main.java");
		final Set<Integer> expectedHashCode = new HashSet<Integer>();
		expectedHashCode.add(getHashCodeOfFile(file));
		return expectedHashCode;
	}

	private Set<Integer> getExpectedHashCodeVirtualMethod() throws CoreException, IOException {
		final Set<Integer> expectedHashCode = new HashSet<Integer>();
		IFile file = featureProject.getProject().getFile("features_expected/testRenameVirtualMethod/Beautiful/Main.java");
		expectedHashCode.add(getHashCodeOfFile(file));
		file = featureProject.getProject().getFile("features_expected/testRenameVirtualMethod/Hello/Main.java");
		expectedHashCode.add(getHashCodeOfFile(file));
		file = featureProject.getProject().getFile("features_expected/testRenameVirtualMethod/Hello/SubMain.java");
		expectedHashCode.add(getHashCodeOfFile(file));
		file = featureProject.getProject().getFile("features_expected/testRenameVirtualMethod/Wonderful/Main.java");
		expectedHashCode.add(getHashCodeOfFile(file));
		file = featureProject.getProject().getFile("features_expected/testRenameVirtualMethod/World/Main.java");
		expectedHashCode.add(getHashCodeOfFile(file));
		return expectedHashCode;
	}

	private Set<Integer> getExpectedHashCodeVirtualMethodInPackage() throws CoreException, IOException {
		final Set<Integer> expectedHashCode = new HashSet<Integer>();
		IFile file = featureProject.getProject().getFile("features_expected/testRenameVirtualMethodInPackage/Hello/ovgu/Main.java");
		expectedHashCode.add(getHashCodeOfFile(file));
		file = featureProject.getProject().getFile("features_expected/testRenameVirtualMethodInPackage/Hello/ovgu/SubMain.java");
		expectedHashCode.add(getHashCodeOfFile(file));
		return expectedHashCode;
	}

	@Override
	protected boolean hasSameType(AbstractSignature signature) {
		return (signature instanceof FujiMethodSignature);
	}

	@Override
	protected RenameRefactoring<FujiMethodSignature> getRefactoring(final String fullSigName) {
		FujiMethodSignature method = (FujiMethodSignature) getNamedSignature(fullSigName);
		return new RenameMethodRefactoring(method, featureProject, null);
	}

}
