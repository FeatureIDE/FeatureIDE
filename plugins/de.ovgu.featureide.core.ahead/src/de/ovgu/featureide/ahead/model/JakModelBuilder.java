/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.ahead.model;

import java.util.LinkedList;

import mixin.AST_Modifiers;
import mixin.AST_ParList;
import mixin.AST_Program;
import mixin.AST_TypeName;
import mixin.AstCursor;
import mixin.AstNode;
import mixin.AstToken;
import mixin.DecNameDim;
import mixin.FldVarDec;
import mixin.MethodDcl;
import mixin.MthDector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;

import de.ovgu.featureide.ahead.AheadCorePlugin;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;

/**
 * This builder builds the JakProjectModel, by extracting features, 
 * methods and fields from classes to build. 
 * 
 * @author Tom Brosch
 * @author Constanze Adler
 */
public class JakModelBuilder {

	private FSTModel model;
	
	private IFolder sourceFolder;

	public JakModelBuilder(IFeatureProject featureProject) {
		if (featureProject != null) {
			FSTModel oldModel = featureProject.getFSTModel();
			if (oldModel != null)
				oldModel.markObsolete();
	
			model = new FSTModel(featureProject.getProjectName());
			featureProject.setFSTModel(model);
		}
	}

	/**
	 * Adds a class to the jak project model
	 * 
	 * @param className
	 *            Name of the class
	 * @param sources
	 *            source files that were composed to build this class
	 * @param composedASTs
	 *            composed ahead ASTs during the composition step
	 * @param ownASTs
	 *            ahead ASTs of each source file without composing
	 */
	public void addClass(String className, LinkedList<IFile> sources,
			AST_Program[] composedASTs, AST_Program[] ownASTs) {
		FSTClass currentClass = null;
		for (IFile file : sources) {
			currentClass = model.addClass(className, file);
		}
		
		try {
			updateAst(currentClass, sources, composedASTs, ownASTs);
		} catch (Throwable e) {
			AheadCorePlugin.getDefault().logError(e);
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.jakprojectmodel.IClass#updateAst(java.util.Vector,
	 * mixin.AST_Program[], mixin.AST_Program[])
	 */
	public void updateAst(FSTClass currentClass, LinkedList<IFile> sources,
			AST_Program[] composedASTs, AST_Program[] ownASTs) {
		IFile currentFile = null;
		AstCursor c = new AstCursor();

		
		
		FSTMethod newMethod = null;
		LinkedList<FSTField> newFields = null;
		int lineNumber = -1;
		currentClass.clear();

		for (int i = 0; i < sources.size(); i++) {
			currentFile = sources.get(i);
			
		
			// Parse the tree and every method that was found add it to
			// both vectors

			for (c.First(ownASTs[i]); c.More(); c.PlusPlus()) {
				if (c.node instanceof MethodDcl) {

					// Get the method from the Ast
					// This method was not new in this file, than just update
					// the own and available flag
					// Put it back to the methodsMap

					newMethod = getMethod((MethodDcl) c.node);
					if (currentClass.contains(newMethod)) {
						newMethod = (FSTMethod) currentClass.get(newMethod);
						currentClass.remove(newMethod);
					}

					lineNumber = getLineNumber(c.node);
					newMethod.setOwn(currentFile);
					newMethod.setLineNumber(currentFile, lineNumber);
					currentClass.add(newMethod);

					c.Sibling();
				}
				if (c.node instanceof FldVarDec) {
					newFields = getFields((FldVarDec) c.node);
					for (FSTField field : newFields) {

						if (currentClass.contains(field)) {
							field = (FSTField) currentClass.get(field);
							currentClass.remove(field);
						}

						field.setOwn(currentFile);
						field.setLineNumber(currentFile, getLineNumber(c.node));
						currentClass.add(field);
					}
					c.Sibling();
				}
				
		
			}
			FSTFeature f = getFeature(currentClass, currentFile);
			if (!model.getFeaturesMap().containsKey(f.getName())) {
				model.getFeaturesMap().put(f.getName(), f);
			}
			else{
				model.getFeaturesMap().get(f.getName()).getClasses().put(currentClass.getName(),currentClass);
			}

		}
	}

	private int getLineNumber(AstNode node) {
		AstCursor cur = new AstCursor();
		for (cur.First(node); cur.More(); cur.PlusPlus())
			if (cur.node != null && cur.node.tok != null
					&& cur.node.tok[0] != null)
				return ((AstToken) cur.node.tok[0]).lineNum();
		return -1;
	}

	private FSTMethod getMethod(MethodDcl methDcl) {
		AstCursor cur = new AstCursor();
		String type = "";
		String name = "";
		String modifiers = "";
		LinkedList<String> paramTypes = new LinkedList<String>();

		// Travers the Subtree and catch the name of the method,
		// its return type and parameter types;

		for (cur.First(methDcl); cur.More(); cur.PlusPlus()) {
			if (cur.node instanceof MthDector) {

				// Get the name of the Method
				name = ((MthDector) cur.node).getQName().GetName();

				// Travers the list of parameters if the method has some
				AST_ParList list = ((MthDector) cur.node).getAST_ParList();
				if (list != null) {
					AstCursor listCur = new AstCursor();
					for (listCur.First(list); listCur.More(); listCur
							.PlusPlus()) {
						if (listCur.node instanceof AST_TypeName) {
							paramTypes.add(((AST_TypeName) listCur.node)
									.GetName());
						}
					}
				}

				cur.Sibling(); // This subtree was complete analysed so we can
				// skip it
			} else if (cur.node instanceof AST_TypeName) {

				// Get the return type of the method
				type = ((AST_TypeName) cur.node).GetName();
				cur.Sibling(); // This subtree was complete analysed so we can
				// skip it
			}
			else if (cur.node instanceof AST_Modifiers) {

				// Get the modifiers of the method
				modifiers = ((AST_Modifiers) cur.node).toString().trim();
				cur.Sibling(); // This subtree was complete analysed so we can
				// skip it
				
			}

		}

		return new FSTMethod(name, paramTypes, type, modifiers);
	}

	private LinkedList<FSTField> getFields(FldVarDec fieldDcl) {
		AstCursor cur = new AstCursor();
		String type = "";
		String modifiers = "";

		LinkedList<FSTField> fields = new LinkedList<FSTField>();

		// Travers the Subtree and get the type and
		// all variable qualifiers

		for (cur.First(fieldDcl); cur.More(); cur.PlusPlus()) {

			if (cur.node instanceof AST_TypeName) {

				// Get the return type of the method
				type = ((AST_TypeName) cur.node).GetName();
				cur.Sibling(); // This subtree was complete analysed so we can
				// skip it
			}
			else if (cur.node instanceof AST_Modifiers) {

				// Get modifiers of the field
				modifiers = ((AST_Modifiers) cur.node).toString().trim();
				cur.Sibling(); // This subtree was complete analysed so we can
				// skip it
			}
			else if (cur.node instanceof DecNameDim) {
				// to do: find out the dimension more correctly
				fields.add(new FSTField(((DecNameDim) cur.node).getQName()
						.GetName(), type, 0, modifiers));
			}

		}

		return fields;
	}
	
	private FSTFeature getFeature(FSTClass currentClass, IFile currentFile){
		sourceFolder = CorePlugin.getFeatureProject(currentFile).getSourceFolder();
		String featureName = getFeature((IFolder)currentFile.getParent());
		FSTFeature f = new FSTFeature(featureName);
		f.getClasses().put(currentClass.getName(), currentClass);
		f.getClasses().get(currentClass.getName()).setFile(currentFile);
		return f;
	}
	
	private String getFeature(IFolder folder) {
		if (((IFolder)folder.getParent()).equals(sourceFolder))
			return folder.getName();
		return getFeature((IFolder)folder.getParent());
	}

	public void clearFeatures() {
		model.getFeaturesMap().clear();
	}
}
