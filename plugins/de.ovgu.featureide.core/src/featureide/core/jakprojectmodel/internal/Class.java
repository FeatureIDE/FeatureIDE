/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.core.jakprojectmodel.internal;

import java.util.LinkedList;
import java.util.TreeMap;

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

import featureide.core.jakprojectmodel.IClass;
import featureide.core.jakprojectmodel.IField;
import featureide.core.jakprojectmodel.IJakElement;
import featureide.core.jakprojectmodel.IMethod;

/**
 * Describes a class of a jak project according to a selected equation
 * 
 * @author Tom Brosch
 * @author Thomas Thuem
 * 
 */
public class Class extends JakElement implements IClass {

	// Only the own AST methods are implemented

	private IFile currentJakfile;

	private TreeMap<String, Method> methods;

	private TreeMap<String, IField> fields;

	private String className;

	private AST_Program[] ownASTs;

	private LinkedList<IFile> sources;

	public Class() {
		this("");
	}

	/**
	 * Creates a new instance of a class
	 * 
	 * @param className The name of the class
	 */
	public Class(String className) {
		this.className = className;
		methods = new TreeMap<String, Method>();
		fields = new TreeMap<String, IField>();
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getNumberOfFields()
	 */
	public int getFieldCount() {
		return fields.size();
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getFields()
	 */
	public IField[] getFields() {
		return fields.values().toArray(new Field[fields.values().size()]);
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getNumberOfMethods()
	 */
	public int getMethodCount() {
		return methods.size();
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getMethods()
	 */
	public IMethod[] getMethods() {
		IMethod[] methodArray = new IMethod[methods.size()];
		int i = 0;
		for (IMethod meth : methods.values())
			methodArray[i++] = meth;
		return methodArray;
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getNumberOfAvailibleFields()
	 */
	public int getAvailableFieldCount() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getAvailibleFields()
	 */
	public IField[] getAvailableFields() {
		return null;
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getNumberOfAvailibleMethods()
	 */
	public int getAvailableMethodCount() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getAvailibleMethods()
	 */
	public IMethod[] getAvailableMethods() {
		return null;
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getNumberOfOwnFields()
	 */
	public int getOwnFieldCount() {
		int i = 0;
		for (IField field : fields.values())
			if (field.isOwn(currentJakfile))
				i++;
		return i;
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getOwnFields()
	 */
	public IField[] getOwnFields() {
		IField[] fieldArray = new Field[getOwnFieldCount()];
		int i = 0;
		for (IField field : fields.values())
			if (field.isOwn(currentJakfile))
				fieldArray[i++] = field;
		return fieldArray;
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getNumberOfOwnMethods()
	 */
	public int getOwnMethodCount() {
		int i = 0;
		for (IMethod meth : methods.values())
			if (meth.isOwn(currentJakfile))
				i++;
		return i;
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getOwnMethods()
	 */
	public IMethod[] getOwnMethods() {
		IMethod[] methodArray = new Method[getOwnMethodCount()];
		int i = 0;
		for (IMethod meth : methods.values()) {
			if (meth.isOwn(currentJakfile))
				methodArray[i++] = meth;
		}
		return methodArray;
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#setJakfile(org.eclipse.core.resources.IFile)
	 */
	public void setJakfile(IFile jakfile) {
		currentJakfile = jakfile;
	}
	
	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getJakfile()
	 */
	public IFile getJakfile() {
		return currentJakfile;
	}

	public String getName() {
		return className;
	}

	public IJakElement[] getChildren() {
		IJakElement[] elements = new IJakElement[getOwnFieldCount()
				+ getOwnMethodCount()];
		IField[] fieldArray = getOwnFields();
		IMethod[] methodArray = getOwnMethods();
		int pos = 0;
		for (int i = 0; i < fieldArray.length; i++, pos++)
			elements[pos] = fieldArray[i];
		for (int i = 0; i < methodArray.length; i++, pos++)
			elements[pos] = methodArray[i];
		return elements;
	}

	public boolean hasChildren() {
		return getOwnMethodCount() + getOwnFieldCount() > 0;
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#updateAst(java.util.Vector, mixin.AST_Program[], mixin.AST_Program[])
	 */
	public void updateAst(LinkedList<IFile> sources, AST_Program[] composedASTs,
			AST_Program[] ownASTs) {
		this.ownASTs = ownASTs;
		this.sources = sources;
	    	IFile currentFile = null;
		AstCursor c = new AstCursor();

		Method newMethod = null;
		LinkedList<Field> newFields = null;
		int lineNumber = -1;
		methods.clear();
		fields.clear();

		for (int i = 0; i < sources.size(); i++) {
			currentFile = sources.get(i);

			// Parse the tree and every method that was found add it to
			// both vectors

			for (c.First(ownASTs[i]); c.More(); c.PlusPlus()) {
				if (c.node instanceof MethodDcl) {

					// Get the method from the Ast
					// This method was not new in this file, than just update
					// the own und availible flag
					// Put it back to the methodsMap

					newMethod = getMethod((MethodDcl) c.node);
					if (methods.containsKey(newMethod.getIdentifier())) {
						newMethod = methods.get(newMethod.getIdentifier());
						methods.remove(newMethod.getIdentifier());
					}
					
					lineNumber = getLineNumber(c.node);
					newMethod.setOwn(currentFile);
					newMethod.setLineNumber(currentFile, lineNumber);
					methods.put(newMethod.getIdentifier(), newMethod);

					c.Sibling();
				}
				if (c.node instanceof FldVarDec) {
					newFields = getFields((FldVarDec) c.node);
					for (IField field : newFields) {

						if (fields.containsKey(field.getIdentifier())) {
							field = fields.get(field.getIdentifier());
							fields.remove(field.getIdentifier());
						}

						field.setOwn(currentFile);
						field.setLineNumber(currentFile,
								getLineNumber(c.node));
						fields.put(field.getIdentifier(), field);
					}
					c.Sibling();
				}
			}

		}
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getASTs()
	 */
	public AST_Program[] getASTs(){
	    return ownASTs;
	}

	/* (non-Javadoc)
	 * @see featureide.core.jakprojectmodel.IClass#getSources()
	 */
	public LinkedList<IFile> getSources(){
	    return sources;
	}

	private int getLineNumber(AstNode node) {
		AstCursor cur = new AstCursor();
		for( cur.First(node); cur.More(); cur.PlusPlus() )
			if (cur.node != null && cur.node.tok != null && cur.node.tok[0] != null)
				return ((AstToken) cur.node.tok[0]).lineNum();
		return -1;
	}

	private Method getMethod(MethodDcl methDcl) {
		AstCursor cur = new AstCursor();
		String type = "";
		String name = "";
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

		}

		return new Method(name, paramTypes, type);
	}

	private LinkedList<Field> getFields(FldVarDec fieldDcl) {
		AstCursor cur = new AstCursor();
		String type = "";

		LinkedList<Field> fields = new LinkedList<Field>();

		// Travers the Subtree and get the type and
		// all variable qualifiers

		for (cur.First(fieldDcl); cur.More(); cur.PlusPlus()) {

			if (cur.node instanceof AST_TypeName) {

				// Get the return type of the method
				type = ((AST_TypeName) cur.node).GetName();
				cur.Sibling(); // This subtree was complete analysed so we can
								// skip it
			} else if (cur.node instanceof DecNameDim) {
				//to do: find out the dimension more correctly
				fields.add(new Field(((DecNameDim) cur.node).getQName()
						.GetName(), type, 0));
			}

		}

		return fields;
	}
}
