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
package de.ovgu.featureide.core.framework;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
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
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;
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
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;

/**
 * TODO description
 * 
 * @author Daniel Hohmann
 */
public class FrameworkModelBuilder {
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
		//		featureProject.setFSTModel(model);
		this.featureProject = featureProject;
	}

	/**
	 * Will build model depending on <code>info.xml</code> inside feature folders<br>
	 * <ul>
	 * <li>May take a moment
	 * <li>Only referenced interfaces inside <code>info.xml</code> will be noted
	 * </ul>
	 * 
	 * @throws CoreException
	 */
	public void buildModel() throws CoreException {
		IFolder featureFolder = featureProject.getSourceFolder();
		IResource[] features = featureFolder.members();
		Map<String, Map<String, List<String>>> featureMap = new HashMap<>();

		for (IResource res : features) {
			if (res instanceof IFolder) {
				Map<String, List<String>> interfaceImplementations = new HashMap<>();
				IFile infoXml = ((IFolder) res).getFile("info.xml");
				if (infoXml.exists()) {
					getInterfaceImplementations(infoXml, interfaceImplementations);
					featureMap.put(res.getName(), interfaceImplementations);
				}
			}
		}
		buildModel(featureMap);
		this.featureProject.setFSTModel(this.model);
	}

	/**
	 * builds model depending on collected information
	 * 
	 * @param featureMap
	 */
	private void buildModel(Map<String, Map<String, List<String>>> featureMap) {
		/** add classes **/
		for (String feature : featureMap.keySet()) {
			model.addFeature(feature);
			System.out.println(feature);
			for (String interfaceName : featureMap.get(feature).keySet()) {
				System.out.println(interfaceName);
				model.addClass(new FSTClass(interfaceName));
				List<String> implementingClasses = featureMap.get(feature).get(interfaceName);
				for (String implementingClass : implementingClasses) {
					IFile classFile = findFile(feature, implementingClass);
					FSTRole role = model.addRole(feature, interfaceName, classFile);
					IJavaProject project = JavaCore.create(featureProject.getProject());
					try {
						System.out.println(implementingClass);
						IType classType = project.findType(implementingClass);
						
						/** Get fields **/
						if(classType == null) {
							FrameworkCorePlugin.getDefault().logWarning(implementingClass + " not found");
							continue;
						}
						for(IField f : classType.getFields()){
							role.getClassFragment().add(new FSTField(f.getElementName(), Signature.toString(f.getTypeSignature()), ""));
						}
						
						/** Get methods **/
						for(IMethod m : classType.getMethods()){
							LinkedList<String> parameterTypes = new LinkedList<>();
							for(String s: m.getParameterTypes()){
								parameterTypes.add(s);
							}
							FSTMethod met = new FSTMethod(m.getElementName(), parameterTypes, Signature.toString(m.getReturnType()), "");
							role.getClassFragment().add(met);
						}
						
					} catch (JavaModelException e) {
						FrameworkCorePlugin.getDefault().logError(e);
					}
				}
			}
		}
	}

	/**
	 * Gives you the class inside the feature folder
	 * 
	 * @param feature
	 * @param implementingClass
	 * @return class file as {@link IFile}
	 */
	private IFile findFile(String feature, String implementingClass) {
		String[] pathSegments = null;
		if (implementingClass.contains(".")) {
			pathSegments = implementingClass.split("[.]");

			IFolder featureFolder = featureProject.getSourceFolder().getFolder(feature);
			IFolder location = featureFolder.getFolder("src");
			for (int i = 0; i < pathSegments.length - 1; i++) {
				location = location.getFolder(pathSegments[i]);
			}
			return location.getFile(pathSegments[pathSegments.length - 1] + ".java");
		} else {
			IFolder featureFolder = featureProject.getSourceFolder().getFolder(feature);
			IFolder location = featureFolder.getFolder("src");
			return location.getFile(implementingClass + ".java");
		}
	}

	/**
	 * @param infoXml
	 * @param interfaceImplementations
	 */
	private void getInterfaceImplementations(IFile infoXml, Map<String, List<String>> interfaceImplementations) {
		Map<String, List<String>> map = readInfoXml(infoXml);
		for (String key : map.keySet()) {
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
		Map<String, List<String>> map = new HashMap<>();
		URL url;
		try {
			url = info.getLocationURI().toURL();

			DocumentBuilderFactory dbFactory = DocumentBuilderFactory.newInstance();
			DocumentBuilder dBuilder = dbFactory.newDocumentBuilder();
			Document doc = dBuilder.parse(url.openStream());

			/** Get all interfaces inside JAR **/
			NodeList nlInterfaces = doc.getElementsByTagName("interface");
			for (int i = 0; i < nlInterfaces.getLength(); i++) {
				Node interfaceNode = nlInterfaces.item(i);
				if (interfaceNode.getNodeType() == Node.ELEMENT_NODE) {
					String interfaceName = ((Element) interfaceNode).getAttribute("id");
					/** Get all implementing classes **/
					NodeList nlClasses = interfaceNode.getChildNodes();
					List<String> listClasses = new ArrayList<>();
					for (int j = 0; j < nlClasses.getLength(); j++) {
						Node classNode = nlClasses.item(j);
						if (classNode.getNodeType() == Node.ELEMENT_NODE) {
							Element e = (Element) classNode;
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
}
