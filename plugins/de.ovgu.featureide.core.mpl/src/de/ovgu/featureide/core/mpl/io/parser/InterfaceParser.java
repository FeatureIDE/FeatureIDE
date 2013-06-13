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
package de.ovgu.featureide.core.mpl.io.parser;

import java.util.LinkedList;

import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.AbstractLineReader;
import de.ovgu.featureide.core.mpl.signature.RoleMap;
import de.ovgu.featureide.core.mpl.signature.ViewTagPool;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.mpl.signature.java.JavaFieldSignature;
import de.ovgu.featureide.core.mpl.signature.java.JavaMethodSignature;
import de.ovgu.featureide.core.mpl.signature.java.JavaRole;
import de.ovgu.featureide.core.mpl.signature.java.JavaClassSignature;

/**
 * Reads a java interfaces file to a {@link JavaClassSignature}.
 * 
 * @author Sebastian Krieter
 */
public class InterfaceParser extends AbstractLineReader<JavaRole> {
	private static final String 
		COMMENT = "//+",
		SEP1 = ",",
		SEP2 = ":";

	private final ViewTagPool viewTagPool;
	private final RoleMap roleMap;

	public InterfaceParser(ViewTagPool viewTagPool, RoleMap roleMap) {
		super();
		this.viewTagPool = viewTagPool;
		this.roleMap = roleMap;
	}

	private String lastTagLine = null;
	private int mode = 0;
	
	private String featureName, type, pckg, className, modifier;
	private boolean hasClassDef = false;
	private final LinkedList<JavaRole> stack = new LinkedList<JavaRole>();
	private final LinkedList<String>
			imports = new LinkedList<String>(),
			implementList = new LinkedList<String>(),
			extendList = new LinkedList<String>();

	public void setFeatureName(String featureName) {
		this.featureName = featureName;
	}

	@Override
	protected boolean prepareRead() {
		mode = 0;
		stack.clear();
		infoObj = null;
		return true;
	}
	
	protected boolean readLine(String line) {
		line = line.trim();
		if (!line.isEmpty()) {
			if (line.startsWith(COMMENT)) {
				createRole();
				lastTagLine = line.substring(3);
			} else if (line.startsWith("/*")) {
				createRole();
			} else {
				switch (mode) {
				case 0: if (line.startsWith("package ")) {
							pckg = line.substring(8, line.length() - 1).trim();
							mode = 1;
							break;
						}
				case 1: if (line.startsWith("import ")) {
	//							line.subSequence(7, line.length() - 1).trim();
							imports.add(line);
						} else {
							parseClass(line);
							mode = 2;
						}
						break;
				case 2: if (line.startsWith("extends ")) {
							int index = line.lastIndexOf('{');
							if (index > -1) {
								line = line.substring(0, index);
							}
							String[] extendElements = line.substring(8).split(",");
							for (int i = 0; i < extendElements.length; i++) {
								extendList.add(extendElements[i].trim());
							}
							mode = 3;
							break;
						}
				case 3: if (line.startsWith("implements ")) {
							int index = line.lastIndexOf('{');
							if (index > -1) {
								line = line.substring(0, index);
							}
							String[] implementElements = line.substring(11).split(",");
							for (int i = 0; i < implementElements.length; i++) {
								implementList.add(implementElements[i].trim());
							}
							mode = 4;
							break;
						}
				case 4: createRole();						
				case 5: if (line.matches("(.*\\s(class|interface)|(class|interface))\\s.*$")) {
							parseClass(line);
							mode = 2;
						} else if (line.endsWith("}")) {
							JavaRole role = stack.pop();
							if (stack.isEmpty()) {
								infoObj = role;
							} else {
								stack.peek().addInnerClass(role);
							}
						} else if (line.endsWith(";")) {
							line = line.substring(0, line.length() - 1).trim();
							
							String parameterString = null;
							boolean isConstructor = false;
							
							if (line.endsWith(")")) {
								int index2 = line.lastIndexOf('(');
								
								parameterString = line.substring(index2 + 1, line.length() - 1).trim();
								line = line.substring(0, index2).trim();
							}
							
							String[] memberElements = line.split(" ");
							int index = memberElements.length - 1;
							
							String memberName = memberElements[index--];
							isConstructor = memberName.equals(stack.peek().getSignature().getName());
							
							if (isConstructor) {
								type = null;
							} else {
								type = memberElements[index--];
							}
							
							modifier = "";
							for (; index >= 0; index--) {
								modifier += memberElements[index] + " ";
							}
							
							if (isConstructor || !modifier.contains("private") || MPLPlugin.PRIVATE_METHODS) {
								if (parameterString != null) {
									LinkedList<String> parameterTypes = new LinkedList<String>();
									if (!parameterString.isEmpty()) {
										String[] parameter = parameterString.split(",");
										for (int i = 0; i < parameter.length; i++) {
											String parameterType = parameter[i].trim();
											parameterType = parameterType.substring(0, parameterType.indexOf(' '));
											parameterTypes.add(parameterType);
										}
									}									
									
									JavaMethodSignature sig = (JavaMethodSignature) roleMap
											.getSignatureRef(new JavaMethodSignature(
													stack.peek().getSignature(), memberName, modifier, 
													type, parameterTypes, isConstructor));
	
									sig.addFeature(featureName);
									stack.peek().addMember(sig);
									parseTags(sig);
								} else {
									JavaFieldSignature sig = (JavaFieldSignature) roleMap
											.getSignatureRef(new JavaFieldSignature(
													stack.peek().getSignature(), 
													memberName,	modifier, type));
									sig.addFeature(featureName);
									stack.peek().addMember(sig);
									parseTags(sig);
								}	
							} else {
								lastTagLine = null;
							}
					}
				}
			}
		}
		return true;
	}
	
	private void createRole() {
		if (hasClassDef) {	
			hasClassDef = false;
			mode = 5;
			
			JavaClassSignature newRoleSig;
			if (stack.isEmpty()) {
				newRoleSig = new JavaClassSignature(null,
						className, modifier, type, pckg);
			} else {
				newRoleSig = new JavaClassSignature(stack.peek().getSignature(),
					className, modifier, type, null);
			}
	
			for (String imp : imports) {
				newRoleSig.addImport(imp);
			}
			for (String extend : extendList) {
				newRoleSig.addExtend(extend);
			}
			for (String implement : implementList) {
				newRoleSig.addImplement(implement);
			}
			imports.clear();
			extendList.clear();
			implementList.clear();
			
			
			JavaClassSignature aSig = (JavaClassSignature) roleMap
					.getSignatureRef(newRoleSig);
			parseTags(aSig);
	
			JavaRole newRole = new JavaRole(featureName, aSig);
			aSig.addFeature(featureName);
			stack.push(newRole);
		}
	}
	
	private void parseClass(String line) {
		hasClassDef = true;
		modifier = "";
		int index = line.lastIndexOf('{');
		if (index > -1) {
			line = line.substring(0, index).trim();
		}
		String[] classElements = line.split(" ");
		for (int i = 0; i < classElements.length; i++) {
			if (classElements[i].equals("class") || classElements[i].equals("interface")) {
				type = classElements[i];
				className = classElements[++i];
				int index2 = className.lastIndexOf('<');
				if (index2 > -1) {
					className = className.substring(0, index2);
				}
			} else {
				modifier += classElements[i] + " ";
			}
		}
	}
	
	private void parseTags(AbstractSignature sig) {
		if (lastTagLine != null) {
			String[] tags = lastTagLine.split(SEP1);
			lastTagLine = null;
			for (String tag : tags) {
				String[] tagElements = tag.trim().split(SEP2);
				switch (tagElements.length) {
				case 1: 
					sig.addViewTag(viewTagPool.getViewTag(tagElements[0]));
					break;
				case 2: 
					try {
						int level = Integer.valueOf(tagElements[1]);
						sig.addViewTag(viewTagPool.getViewTag(tagElements[0], level));
					} catch (NumberFormatException e) {
						return;
					}
				}
			}
		}
	}
}
