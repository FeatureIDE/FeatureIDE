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
package de.ovgu.featureide.featurehouse.refactoring.pullUp;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.prop4j.Literal;

import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractClassSignature;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.featurehouse.refactoring.RefactoringUtil;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiFieldSignature;
import de.ovgu.featureide.featurehouse.signature.fuji.FujiMethodSignature;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * TODO description
 * 
 * @author steffen
 */
public class FeatureSignatureHierarchyCreator {

	private final AbstractClassSignature destinationType;
	private final ProjectSignatures projectSignatures;
	private final AbstractSignature[] pullUpSignatures;

	public FeatureSignatureHierarchyCreator(final ExtendedPullUpSignature destinationType, final ProjectSignatures projectSignatures,
			AbstractSignature[] abstractSignatures) {
		this.destinationType = (AbstractClassSignature) destinationType.getSignature();
		this.projectSignatures = projectSignatures;
		this.pullUpSignatures = abstractSignatures;
	}

	public Set<FeatureSignatureHierarchy> createFeatureHierarchies() {
		Set<FeatureSignatureHierarchy> hierarchies = new HashSet<>();
		for (AFeatureData featureData : destinationType.getFeatureData()) {
			hierarchies.add(createFeatureHierarchy(featureData.getID()));
		}

		return hierarchies;
	}

	private FeatureSignatureHierarchy createFeatureHierarchy(final int featureId) {
		final String featureName = projectSignatures.getFeatureName(featureId);
		FeatureSignatureHierarchy hierarchy = new FeatureSignatureHierarchy(getFeature(featureName), featureId);

		final Map<String, AbstractClassSignature> classes = RefactoringUtil.getClasses(projectSignatures);
		for (AbstractClassSignature classSig : classes.values()) {
			if (isCorrectFeatureIdAndPackage(classSig, featureId, destinationType.getPackage()) && classSig.getExtendList().size() == 0) {
				ExtendedPullUpSignature extendSignature = new ExtendedPullUpSignature(classSig, featureId);
				hierarchy.addChild(extendSignature);
				addSubClassesAndMembers(extendSignature, classes, destinationType.getPackage());
			}
		}

		return hierarchy;
	}

	private IFeature getFeature(String featureName) {
		return projectSignatures.getFeatureModel().getFeature(featureName);
	}

	private void addSubClassesAndMembers(final ExtendedPullUpSignature parentExtendSignature, final Map<String, AbstractClassSignature> classes, String pkg) {

		if (!(parentExtendSignature.getSignature() instanceof AbstractClassSignature)) return;

		final AbstractClassSignature classSig = (AbstractClassSignature) parentExtendSignature.getSignature();
		for (String subClass : classSig.getSubClassesList()) {
			AbstractClassSignature subclassSig = classes.get(subClass);

			final int featureId = parentExtendSignature.getFeatureId();
			if (isCorrectFeatureIdAndPackage(subclassSig, featureId, pkg)) {
				ExtendedPullUpSignature childExtendSignature = new ExtendedPullUpSignature(subclassSig, featureId);
				childExtendSignature.setParent(parentExtendSignature);
				parentExtendSignature.addChild(childExtendSignature);
				addSubClassesAndMembers(childExtendSignature, classes, pkg);
			}
		}

		addMethods(parentExtendSignature);
		addFields(parentExtendSignature);
	}

	private void addMethods(ExtendedPullUpSignature parentExtendSignature) {

		if (!(parentExtendSignature.getSignature() instanceof AbstractClassSignature)) return;

		final AbstractClassSignature classSig = (AbstractClassSignature) parentExtendSignature.getSignature();
		final int featureId = parentExtendSignature.getFeatureId();

		for (AbstractSignature pullUpMember : pullUpSignatures) {
			if (!(pullUpMember instanceof FujiMethodSignature)) continue;

			for (AbstractMethodSignature method : classSig.getMethods()) {

				for (AFeatureData featureData : method.getFeatureData()) {
					if (featureData.hasID(featureId) && RefactoringUtil.hasSameName(method, pullUpMember)
						&& RefactoringUtil.hasSameParameters((FujiMethodSignature) pullUpMember, (FujiMethodSignature) method)
						&& RefactoringUtil.hasSameReturnType((FujiMethodSignature) pullUpMember, (FujiMethodSignature) method)) {
						final ExtendedPullUpSignature childExtendSignature = new ExtendedPullUpSignature(method, featureId);
						childExtendSignature.setParent(parentExtendSignature);
						parentExtendSignature.addChild(childExtendSignature);
					}
				}
			}
		}
	}

	private void addFields(ExtendedPullUpSignature parentExtendSignature) {

		if (!(parentExtendSignature.getSignature() instanceof AbstractClassSignature)) return;

		final AbstractClassSignature classSig = (AbstractClassSignature) parentExtendSignature.getSignature();
		final int featureId = parentExtendSignature.getFeatureId();

		for (AbstractSignature pullUpMember : pullUpSignatures) {
			if (!(pullUpMember instanceof FujiFieldSignature)) continue;

			for (AbstractFieldSignature field : classSig.getFields()) {

				for (AFeatureData featureData : field.getFeatureData()) {
					if (featureData.hasID(featureId) && RefactoringUtil.hasSameName(field, pullUpMember)) {
						final ExtendedPullUpSignature childExtendSignature = new ExtendedPullUpSignature(field, featureId);
						childExtendSignature.setParent(parentExtendSignature);
						parentExtendSignature.addChild(childExtendSignature);
					}
				}
			}
		}
	}

	private boolean isCorrectFeatureIdAndPackage(AbstractClassSignature classSig, int featureId, String pkg) {
		for (AFeatureData featureData : classSig.getFeatureData()) {
			if (featureData.hasID(featureId) && classSig.getPackage().equals(pkg)) return true;
		}

		return false;
	}
}
