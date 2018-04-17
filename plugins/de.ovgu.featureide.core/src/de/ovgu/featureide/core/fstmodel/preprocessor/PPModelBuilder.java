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
package de.ovgu.featureide.core.fstmodel.preprocessor;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.preprocessor.PPComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.IRoleElement;
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.functional.Functional;

/**
 * Build the FSTModel for preprocessor projects.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke (Feature Interface)
 */
public class PPModelBuilder {

	protected final IFeatureProject featureProject;

	protected FSTModelForPP model;
	protected FSTModel modelOutline;
	protected Collection<String> featureNames = Collections.emptyList();

	public PPModelBuilder(IFeatureProject featureProject) {
		model = new FSTModelForPP(featureProject);
		modelOutline = new FSTModel(featureProject);

		featureProject.setFSTModel(model);
		this.featureProject = featureProject;
	}

	public void buildModel() {
		model.reset();
		modelOutline.reset();

		featureNames = Functional.toList(FeatureUtils.getConcreteFeatureNames(featureProject.getFeatureModel()));
		for (final String featureName : featureNames) {
			model.addFeature(featureName);
			modelOutline.addFeature(featureName);
		}
		try {
			buildModel(featureProject.getSourceFolder(), featureProject.getSourcePath());
		} catch (final CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
		featureProject.setFSTModel(model);
	}

	protected IFile currentFile = null;

	/**
	 * @param folder
	 * @param packageName
	 * @throws CoreException
	 */
	private void buildModel(IFolder folder, String packageName) throws CoreException {
		for (final IResource res : folder.members()) {
			if (res instanceof IFolder) {
				buildModel((IFolder) res, packageName.isEmpty() ? res.getName() : packageName + "/" + res.getName());
			} else if (res instanceof IFile) {
				currentFile = (IFile) res;
				final String text = getText(currentFile);
				final String className = packageName.isEmpty() ? res.getName() : packageName + "/" + res.getName();

				final Vector<String> lines = PPComposerExtensionClass.loadStringsFromFile(currentFile);
				boolean classAdded = false;
				for (final String feature : featureNames) {
					if (containsFeature(text, feature)) {
						model.addRole(feature, model.getAbsoluteClassName(currentFile), currentFile);
						classAdded = true;
					}
				}
				if (classAdded) {
					final LinkedList<FSTDirective> directives = buildModelDirectivesForFile(lines);
					addRoleElementsToDirectives(directives, currentFile, className);
					addDirectivesToRoleElement(directives, currentFile, className);

					addDirectivesToModel(directives, currentFile, className);
				} else {
					// add class without annotations
					model.addClass(new FSTClass(className));
				}
			}
		}
	}

	private void addDirectivesToModel(LinkedList<FSTDirective> list, IFile res, String className) {
		for (final FSTDirective d : list) {
			for (final String featureName : d.getFeatureNames()) {
				if (!featureNames.contains(featureName)) {
					continue;
				}
				final FSTRole role = model.addRole(featureName, model.getAbsoluteClassName(res), res);// addRole(getFeatureName(d.getExpression()),
																										// res.getName(), res);
				role.add(d);
				addDirectivesToModel(d.getChildrenList(), res, className);
			}

		}
	}

	private void addRoleElementsToDirectives(LinkedList<FSTDirective> directives, IFile res, String className) {
		for (final FSTDirective fstDirective : directives) {
			final List<AbstractSignature> addedSig = new ArrayList<>();
			final List<AbstractSignature> includedSig = fstDirective.getIncludedSig();
			if (includedSig != null) {
				for (final AbstractSignature abstractSignature : includedSig) {
					if (abstractSignature instanceof AbstractMethodSignature) {
						final AbstractMethodSignature tmp = (AbstractMethodSignature) abstractSignature;
						final FSTMethod method =
							new FSTMethod(tmp.getName(), new LinkedList<>(tmp.getParameterTypes()), tmp.getReturnType(), tmp.getModifiers()[0]);
						method.setLine(tmp.getStartLine());

						for (final String featureName : fstDirective.getFeatureNames()) {
							final FSTRole role = model.addRole(featureName, model.getAbsoluteClassName(res), res);
							role.add(fstDirective);
						}
						fstDirective.addChild(method);
						method.setRole(fstDirective.getRole());

						addedSig.add(abstractSignature);
					} else if (abstractSignature instanceof AbstractFieldSignature) {
						final AbstractFieldSignature tmp = (AbstractFieldSignature) abstractSignature;
						final FSTField field = new FSTField(tmp.getName(), tmp.getType(), tmp.getModifiers()[0]);
						for (final String featureName : fstDirective.getFeatureNames()) {
							final FSTRole role = model.addRole(featureName, className, res);
							role.add(fstDirective);
						}
						fstDirective.addChild(field);
						field.setRole(fstDirective.getRole());
					}
				}
			}
			final FSTDirective[] children = fstDirective.getChildren();
			if (children != null) {
				for (final FSTDirective roleChild : children) {
					if (addedSig.isEmpty() || ((roleChild.getInsideOfSig() != null) && !roleChild.getInsideOfSig().containsAll(addedSig))) {
						fstDirective.addChild((RoleElement<?>) roleChild);
					}
				}
				addRoleElementsToDirectives(new LinkedList<FSTDirective>(Arrays.asList(children)), currentFile, className);
			}
			addedSig.clear();
		}
	}

	private void addDirectivesToRoleElement(LinkedList<FSTDirective> list, IFile res, String className) {
		for (final FSTDirective d : list) {
			for (final String featureName : d.getFeatureNames()) {
				final FSTRole role = modelOutline.addRole(featureName, modelOutline.getAbsoluteClassName(res), res);

				final List<AbstractSignature> sig = d.getInsideOfSig();
				List<AbstractSignature> includedParentSig = new ArrayList<>();
				final FSTDirective parent = d.getParent();
				if (parent != null) {
					includedParentSig = parent.getIncludedSig();
				}
				boolean added = false;
				if (sig != null) {
					for (final AbstractSignature abstractSignature : sig) {
						if (includedParentSig.contains(abstractSignature)) {
							final RoleElement<?>[] roleElementChildren = parent.getRoleElementChildren();
							for (final RoleElement<?> roleElement : roleElementChildren) {
								if (roleElement.getName().equals(abstractSignature.getName())) {
									if (roleElement instanceof FSTMethod) {
										((FSTMethod) roleElement).add(d);
										roleElement.setLine(abstractSignature.getStartLine());
										final IRoleElement paren = roleElement.getParent();
										role.getClassFragment().add(roleElement);
										roleElement.setParent(paren);
										added = true;
									}
								}
							}
						} else {

							if (abstractSignature instanceof AbstractMethodSignature) {
								final AbstractMethodSignature tmp = (AbstractMethodSignature) abstractSignature;

								for (final FSTMethod method : role.getClassFragment().getMethods()) {
									if (method.getName().equals(tmp.getName())) {
										method.add(d);
										method.setLine(tmp.getStartLine());
										added = true;
										break;
									}
								}

								if (!added) {
									final FSTMethod method =
										new FSTMethod(tmp.getName(), new LinkedList<>(tmp.getParameterTypes()), tmp.getReturnType(), "tetw");
									method.setLine(tmp.getStartLine());
									role.getClassFragment().add(method);
									method.add(d);
									added = true;
								}
							}
						}
					}
				}
				if (!added) {
					role.add(d);
				}
				addDirectivesToRoleElement(d.getChildrenList(), res, className);
			}
		}
	}

	protected List<String> getFeatureNames(String expression) {
		expression = expression.replaceAll("[(]", "");
		final List<String> featureNameList = new LinkedList<String>();
		featureNameList.add(expression.replaceAll("[)]", "").trim());
		return featureNameList;
	}

	/**
	 * This method should be implemented by preprocessor plug-ins. Adds directives to model.
	 *
	 * @param currentClass The current class.
	 * @param res The current file.
	 */
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		return new LinkedList<FSTDirective>();
	}

	/**
	 * This method should be implemented by preprocessor plug-ins. Return true if the file contains the feature.
	 *
	 * @param text The file text.
	 * @param feature The current feature.
	 */
	protected boolean containsFeature(String text, String feature) {
		return text.contains(feature);
	}

	/**
	 * @param iFile
	 */
	private String getText(IFile iFile) {
		Scanner scanner = null;
		try {
			final File file = iFile.getRawLocation().toFile();
			final StringBuilder fileText = new StringBuilder();
			scanner = new Scanner(file, "UTF-8");
			while (scanner.hasNext()) {
				fileText.append(scanner.nextLine());
				fileText.append("\r\n");
			}
			return fileText.toString();
		} catch (final FileNotFoundException e) {
			CorePlugin.getDefault().logError(e);
		} finally {
			if (scanner != null) {
				scanner.close();
			}
		}
		return "";
	}

}
