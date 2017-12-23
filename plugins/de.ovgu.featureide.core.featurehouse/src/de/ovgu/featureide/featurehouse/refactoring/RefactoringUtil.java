/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.refactoring;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.CompilationUnit;

import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiClassSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class RefactoringUtil {

	public static CompilationUnit parseUnit(final String absoluteFilePath) {

		try {
			final ASTParser parser = ASTParser.newParser(AST.JLS4);
			parser.setKind(ASTParser.K_COMPILATION_UNIT);
			byte[] encoded = Files.readAllBytes(Paths.get(absoluteFilePath));
			final String content = new String(encoded, StandardCharsets.UTF_8);
			parser.setCompilerOptions(JavaCore.getOptions());

			final String[] classpath = java.lang.System.getProperty("java.class.path").split(";");
			final int index = absoluteFilePath.lastIndexOf(File.separator);
			final String path = absoluteFilePath.substring(0, index);
			parser.setUnitName(absoluteFilePath.substring(index + 1));

			parser.setEnvironment(classpath, new String[] { path }, new String[] { StandardCharsets.UTF_8.name() }, true);
			parser.setSource(content.toCharArray());
			parser.setResolveBindings(true);
			parser.setBindingsRecovery(true);

			return (CompilationUnit) parser.createAST(null);
		} catch (IOException e) {
			e.printStackTrace();
		}
		return null;
	}

	public static boolean hasSamePackage(final AbstractSignature signature1, final AbstractSignature signature2) {

		final String sigPackage1 = getPackage(signature1);
		final String sigPackage2 = getPackage(signature2);

		return sigPackage1.equals(sigPackage2);
	}

	public static String getPackage(final AbstractSignature signature) {
		if (signature instanceof FujiClassSignature) return ((FujiClassSignature) signature).getPackage();
		else return signature.getParent().getPackage();
	}

	public static boolean hasSameName(final AbstractSignature signature1, final AbstractSignature signature2) {
		return hasSameName(signature1.getName(), signature2.getName());
	}

	public static boolean hasSameName(final AbstractSignature signature, final String name) {
		return signature.getName().equals(name);
	}

	private static boolean hasSameName(final String name1, final String name2) {
		return name1.equals(name2);
	}

	public static boolean hasSameParameters(final FujiMethodSignature signature1, final FujiMethodSignature signature2) {
		List<String> parameterTypes1 = signature1.getParameterTypes();
		List<String> parameterTypes2 = signature2.getParameterTypes();

		return parameterTypes1.equals(parameterTypes2);
	}

	public static boolean hasSameReturnType(final FujiMethodSignature signature1, final FujiMethodSignature signature2) {
		return signature1.getReturnType().equals(signature2.getReturnType());
	}

	/**
	 * Returns <code>true</code> if the method could be a virtual method, i.e. if it is not a constructor, is private, or is static.
	 *
	 * @param method a method
	 * @return <code>true</code> if the method could a virtual method
	 */
	public static boolean isVirtual(AbstractMethodSignature method) {
		if (method.isConstructor()) return false;
		if (method.isPrivate()) return false;
		if (method.isStatic()) return false;
		return true;
	}

	public static Map<String, AbstractClassSignature> getClasses(final ProjectSignatures signatures) {
		final Map<String, AbstractClassSignature> classes = new HashMap<>();

		final SignatureIterator iter = signatures.iterator();
		while (iter.hasNext()) {
			final AbstractSignature signature = iter.next();
			if (signature instanceof AbstractClassSignature) {
				String fullName = signature.getFullName();
				if (fullName.startsWith(".")) fullName = fullName.substring(1);
				classes.put(fullName, (AbstractClassSignature) signature);
			}
		}

		return classes;
	}

	public static IFile getFile(final String relativePath) {
		return ResourcesPlugin.getWorkspace().getRoot().getFileForLocation(Path.fromOSString(relativePath));
	}

	public static ICompilationUnit getCompilationUnit(final String relativePath) {
		final IFile file = RefactoringUtil.getFile(relativePath);

		if ((file == null) || ((file != null) && !file.isAccessible())) return null;

		return JavaCore.createCompilationUnitFrom(file);
	}

	public static IFeature getFeatureForId(ProjectSignatures projectSignatures, int featureId) {
		final String featureName = projectSignatures.getFeatureName(featureId);
		return projectSignatures.getFeatureModel().getFeature(featureName);
	}

	public static Set<AbstractSignature> getMatchedSignaturesForClass(Set<? extends AbstractSignature> signatures, String matchingFile) {
		Set<AbstractSignature> matchedSignatures = new HashSet<>();
		for (AbstractSignature signature : signatures) {
			matchedSignatures.addAll(getMatchedSignature(signature, matchingFile));
		}
		return matchedSignatures;
	}

	private static Set<AbstractSignature> getMatchedSignature(AbstractSignature signature, String matchingFile) {
		Set<AbstractSignature> matchedSignatures = new HashSet<>();
		for (AFeatureData featureData : signature.getFeatureData()) {
			if (featureData.getAbsoluteFilePath().equals(matchingFile)) {
				matchedSignatures.add(signature);
				break;
			}
		}
		return matchedSignatures;
	}

	public static Set<AbstractSignature> getIncludedMatchingSignaturesForFile(AbstractClassSignature classSignature, String matchingFile) {
		Set<AbstractSignature> matchedSignatures = getMatchedSignaturesForClass(classSignature.getMethods(), matchingFile);
		matchedSignatures.addAll(getMatchedSignaturesForClass(classSignature.getFields(), matchingFile));
		matchedSignatures.addAll(getMatchedSignature(classSignature, matchingFile));

		return matchedSignatures;
	}

}
