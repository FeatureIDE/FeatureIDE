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
package de.ovgu.featureide.core.framework;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.Flags;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.framework.activator.FrameworkCorePlugin;
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;

/**
 * Class for building FSTModel
 *
 * @author Daniel Hohmann
 */
public class FrameworkModelBuilder {

	@SuppressWarnings("deprecation")
	private static final int AST_Type = AST.JLS4;
	private FSTModel model;
	private IFeatureProject featureProject;

	public FrameworkModelBuilder(IFeatureProject featureProject) {
		if (featureProject == null) {
			return;
		}
		model = featureProject.getFSTModel();
		if (model == null) {
			model = new FSTModel(featureProject);
		}
		// featureProject.setFSTModel(model);
		this.featureProject = featureProject;
	}

	/**
	 * Will build model depending on <code>info.xml</code> inside feature folders<br> <ul> <li>May take a moment <li>Only referenced interfaces inside
	 * <code>info.xml</code> will be noted </ul>
	 *
	 * @throws CoreException
	 */
	public void buildModel() throws CoreException {
		final IFolder featureFolder = featureProject.getSourceFolder();
		final IResource[] features = featureFolder.members();
		final Map<String, Map<String, List<String>>> featureMap = new HashMap<>();

		for (final IResource res : features) {
			if (res instanceof IFolder) {
				final Map<String, List<String>> interfaceImplementations = new HashMap<>();
				final IFile infoXml = ((IFolder) res).getFile("info.xml");
				if (infoXml.exists()) {
					getInterfaceImplementations(infoXml, interfaceImplementations);
					featureMap.put(res.getName(), interfaceImplementations);
				}
			}
		}
		buildModel(featureMap);
		featureProject.setFSTModel(model);
	}

	/**
	 * builds model depending on collected information
	 *
	 * @param featureMap
	 */
	private void buildModel(Map<String, Map<String, List<String>>> featureMap) {
		/** add classes **/
		for (final String feature : featureMap.keySet()) {
			model.addFeature(feature);
			for (final String interfaceName : featureMap.get(feature).keySet()) {
				model.addClass(new FSTClass(interfaceName));
				final List<String> implementingClasses = featureMap.get(feature).get(interfaceName);
				for (final String implementingClass : implementingClasses) {
					addRole(feature, interfaceName, implementingClass);
				}
			}
		}
	}

	/**
	 * @param feature
	 * @param interfaceName
	 * @param implementingClass
	 */
	private void addRole(final String feature, final String interfaceName, final String implementingClass) {

		final IFolder featureFolder = featureProject.getSourceFolder().getFolder(feature);
		final IFolder location = featureFolder.getFolder("src");

		/** Get interface methods **/
		final IFile interfaceFile = findFile(featureProject.getBuildFolder(), interfaceName);
		String interfaceContent;
		MyASTVisitor interfaceVisitor = null;
		try {
			interfaceContent = fileToString(interfaceFile);
			final ASTParser intefaceParser = ASTParser.newParser(AST_Type);
			intefaceParser.setSource(interfaceContent.toCharArray());
			intefaceParser.setKind(ASTParser.K_COMPILATION_UNIT);

			final CompilationUnit interfaceUnit = (CompilationUnit) intefaceParser.createAST(null);
			interfaceVisitor = new MyASTVisitor(true);
			interfaceUnit.accept(interfaceVisitor);
		} catch (final IOException e) {
			// Interface not found
			FrameworkCorePlugin.getDefault().logWarning(e.getMessage());
			return;
		}

		final IFile classFile = findFile(location, implementingClass);
		final FSTRole role = model.addRole(feature, interfaceName, classFile);
		final IJavaProject project = JavaCore.create(featureProject.getProject());
		try {
			final IType classType = project.findType(implementingClass);
			/** ASTNodes **/
			final String fileContent = fileToString(classFile);
			final ASTParser parser = ASTParser.newParser(AST_Type);
			parser.setSource(fileContent.toCharArray());
			parser.setKind(ASTParser.K_COMPILATION_UNIT);

			final CompilationUnit unit = (CompilationUnit) parser.createAST(null);
			final MyASTVisitor visitor = new MyASTVisitor();
			unit.accept(visitor);

			/** Get fields **/
			if (classType == null) {
				FrameworkCorePlugin.getDefault().logWarning(implementingClass + " not found");
				return;
			}
			for (final IField f : classType.getFields()) {
				final FSTField field = new FSTField(f.getElementName(), Signature.toString(f.getTypeSignature()), "");
				if (visitor.getData(f) != null) {
					field.setLine(unit.getLineNumber(visitor.getData(f).intValue()));
				}
				role.getClassFragment().add(field);
			}

			/** Get methods **/
			for (final IMethod m : classType.getMethods()) {
				final LinkedList<String> parameterTypes = new LinkedList<>();
				for (final String s : m.getParameterTypes()) {
					parameterTypes.add(s);
				}

				final boolean isRefinement = calculateRefinement(parameterTypes, interfaceVisitor.getMethodSignature(m));
				final FSTMethod met = new FSTMethod(m.getElementName(), parameterTypes, Signature.toString(m.getReturnType()), getModifiers(m)) {

					/**
					 * Returns true, if method is from interface or abstract class
					 */
					@Override
					public boolean inRefinementGroup() {
						return isRefinement;
					}
				};
				if (visitor.getData(m) != null) {
					met.setLine(unit.getLineNumber(visitor.getData(m).getStartPosition()));
					met.setEndLine(unit.getLineNumber((visitor.getData(m).getStartPosition() + visitor.getData(m).getLength())));
				}
				role.getClassFragment().add(met);

			}

		} catch (JavaModelException | IOException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * Calculates highlighting.
	 *
	 * @param parameterTypes
	 * @param methodSignature
	 * @return
	 */
	private boolean calculateRefinement(List<String> parameterTypes, List<String> methodSignature) {
		if (methodSignature == null) {
			return false;
		}
		int i = 0;
		for (final String s : parameterTypes) {
			if (!methodSignature.contains(s)) {
				return false;
			}
			i++;
		}
		if (i != methodSignature.size()) {
			return false;
		}
		return true;
	}

	/**
	 * @param m - Method
	 * @return String representation of method modifiers
	 * @throws JavaModelException
	 */
	private String getModifiers(IMethod m) throws JavaModelException {
		final StringBuilder b = new StringBuilder();
		final int flags = m.getFlags();
		if (Flags.isPublic(flags)) {
			b.append("public ");
		}
		if (Flags.isPrivate(flags)) {
			b.append("private ");
		}
		if (Flags.isProtected(flags)) {
			b.append("protected ");
		}
		if (Flags.isAbstract(flags)) {
			b.append("abstract ");
		}
		if (Flags.isStatic(flags)) {
			b.append("static ");
		}
		return b.toString();
	}

	/**
	 * Gives you the java file inside the given location
	 *
	 * @param feature
	 * @param implementingClass
	 * @return class file as {@link IFile}
	 */
	private IFile findFile(IFolder location, String implementingClass) {
		String[] pathSegments = null;
		if (implementingClass.contains(".")) {
			pathSegments = implementingClass.split("[.]");
			for (int i = 0; i < (pathSegments.length - 1); i++) {
				location = location.getFolder(pathSegments[i]);
			}
			return location.getFile(pathSegments[pathSegments.length - 1] + ".java");
		} else {
			return location.getFile(implementingClass + ".java");
		}
	}

	/**
	 * @param infoXml
	 * @param interfaceImplementations
	 */
	private void getInterfaceImplementations(IFile infoXml, Map<String, List<String>> interfaceImplementations) {
		final Map<String, List<String>> map = readInfoXml(infoXml);
		for (final String key : map.keySet()) {
			if (interfaceImplementations.containsKey(key)) {
				interfaceImplementations.get(key).addAll(map.get(key));
			} else {
				interfaceImplementations.put(key, map.get(key));
			}
		}
	}

	/**
	 * Reads the info.xml file inside a jar
	 *
	 * @param info - info.xml file inside a jar
	 * @return Map with name of interfaces and implementing classes
	 */
	private Map<String, List<String>> readInfoXml(IFile info) {
		final Map<String, List<String>> map = new HashMap<>();
		URL url;
		try {
			url = info.getLocationURI().toURL();

			final DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
			final DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
			final Document doc = dBuilder.parse(url.openStream());

			/** Get all interfaces inside JAR **/
			final NodeList nlInterfaces = doc.getElementsByTagName("interface");
			for (int i = 0; i < nlInterfaces.getLength(); i++) {
				final Node interfaceNode = nlInterfaces.item(i);
				if (interfaceNode.getNodeType() == Node.ELEMENT_NODE) {
					final String interfaceName = ((Element) interfaceNode).getAttribute("id");
					/** Get all implementing classes **/
					final NodeList nlClasses = interfaceNode.getChildNodes();
					final List<String> listClasses = new ArrayList<>();
					for (int j = 0; j < nlClasses.getLength(); j++) {
						final Node classNode = nlClasses.item(j);
						if (classNode.getNodeType() == Node.ELEMENT_NODE) {
							final Element e = (Element) classNode;
							listClasses.add(e.getTextContent());
						}
					}
					/** Update map at key **/
					if (map.containsKey(interfaceName) && !map.get(interfaceName).isEmpty()) {
						map.get(interfaceName).addAll(listClasses);
					} else {
						map.put(interfaceName, listClasses);
					}
				}
			}
		} catch (ParserConfigurationException | SAXException | IOException e) {
			FrameworkCorePlugin.getDefault().logError(e);
		}

		return map;
	}

	/**
	 * Iterates over a file and turns its content into a string
	 *
	 * @param classFile
	 * @return null, if classFile is {@code null}
	 * @throws IOException
	 */
	private String fileToString(IFile classFile) throws IOException {
		if (classFile == null) {
			return null;
		}
		final String filePath = classFile.getLocation().toOSString();
		final StringBuilder fileData = new StringBuilder(1000);
		final BufferedReader reader = new BufferedReader(new FileReader(filePath));

		char[] buf = new char[10];
		int numRead = 0;
		while ((numRead = reader.read(buf)) != -1) {
			final String readData = String.valueOf(buf, 0, numRead);
			fileData.append(readData);
			buf = new char[1024];
		}

		reader.close();

		return fileData.toString();
	}

	/**
	 *
	 * ASTVisitor iterating over java file
	 *
	 * @author Daniel Hohmann
	 */
	private class MyASTVisitor extends ASTVisitor {

		Map<String, Block> methods;
		Map<String, Integer> fields;
		Map<String, List<String>> interfaceMethods;
		boolean iterateOverInterface;

		/**
		 * Constructor for visitor iterating over class
		 */
		MyASTVisitor() {
			this(false);

		}

		/**
		 *
		 * @param b - {@code true}, if visitor iterates over interface
		 */
		MyASTVisitor(boolean b) {
			iterateOverInterface = b;
			methods = new HashMap<>();
			fields = new HashMap<>();
			interfaceMethods = new HashMap<>();
		}

		/**
		 * Visit methods depending on ast node structure <ul> <li>if structure is java structure, it will save body of method <li>if structure is interface
		 * structure, it will save parameters </ul>
		 */
		@Override
		public boolean visit(MethodDeclaration node) {
			if (!iterateOverInterface) {
				final Block body = node.getBody();
				methods.put(node.getName().getFullyQualifiedName(), body);
				return false;
			}
			final List<String> parameters = new ArrayList<>();
			for (final Object o : node.parameters()) {
				final SingleVariableDeclaration variable = (SingleVariableDeclaration) o;
				String type = variable.getStructuralProperty(SingleVariableDeclaration.TYPE_PROPERTY).toString();
				for (int i = 0; i < variable.getExtraDimensions(); i++) {
					type += "[]";
				}
				parameters.add(type);
			}
			interfaceMethods.put(node.getName().getIdentifier(), parameters);
			return false;
		}

		/**
		 * Visit Fields
		 */
		@Override
		public boolean visit(FieldDeclaration node) {
			fields.put(node.toString(), Integer.valueOf(node.getStartPosition() + node.getLength()));
			return false;
		}

		/**
		 * Getter for data for specified method
		 *
		 * @param m - method
		 * @return block of method
		 */
		public Block getData(IMethod m) {
			return methods.get(m.getElementName());
		}

		/**
		 * Getter for data for specified field
		 *
		 * @param f - field
		 * @return line number as {@code Integer}
		 */
		public Integer getData(IField f) {
			return fields.get(f.getElementName());
		}

		/**
		 * Getter for method signature for method with same name
		 *
		 * @param m
		 * @return
		 */
		public List<String> getMethodSignature(IMethod m) {
			if (!iterateOverInterface) {
				return Collections.<String> emptyList();
			}
			return interfaceMethods.get(m.getElementName());
		}
	}
}
