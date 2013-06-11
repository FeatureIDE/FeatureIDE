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
package de.ovgu.featureide.core.mpl.signature.java;

import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClass;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassSignature;

/**
 * Holds the java signature of a class.
 * 
 * @author Sebastian Krieter
 */
public class JavaClass extends AbstractClass {
	
	public JavaClass(AbstractClassSignature signature) {
		super(signature);
	}
	
	@Override
	public String toString() {
		return JavaStringBuilder.getClassString(this, false);
	}

	@Override
	public String toShortString() {
		return JavaStringBuilder.getClassString(this, true);
	}
		
//	public LinkedList<String> getLines2(boolean shortString) {
//		final LinkedList<String> lines = new LinkedList<String>();
//		
//		if (!signature.getPackage().isEmpty()) {
//			lines.add("package " + signature.getPackage() + ";");
//		}
//		if (!importList.isEmpty()) {
//			for (String importClass : importList) {
//				lines.add(importClass);
//			}
//			lines.add("");
//		}
//		
//		lines.add(signature.toString());
//
//		if (!extendList.isEmpty()) {
//			String extend = (shortString) ? "\t\textends " : " extends ";
//			for (String ext : extendList) {
//				extend += ext + ",";
//			}
//			lines.add(extend.substring(0, extend.length() - 1));
//		}
//
//		if (!implementList.isEmpty()) {
//			String implement = (shortString) ? "\t\timplements " : " implements ";
//			for (String impl : implementList) {
//				implement += impl + ",";
//			}
//			lines.add(implement.substring(0, implement.length() - 1));
//		}
//		
//		lines.add("{");
//		
//		if (!innerClasses.isEmpty()) {
//			for (AbstractClass innerClass : innerClasses.values()) {
//				final StringBuilder sb = new StringBuilder();
//				for (String line : innerClass.getLines(shortString)) {
//					sb.append('\t');
//					sb.append(line);
//					sb.append(LINE_SEPARATOR);
//				}
//				lines.add(sb.toString());
//			}
//			lines.add("");
//		}
//
//		if (!fields.isEmpty()) {
//			for (JavaFieldSignature field : fields) {
//				lines.add(" /* ext: " + field.isExt() +" */ ");
//				if (field.hasViewTags()) {
//					StringBuilder sb = new StringBuilder("\t//+ ");
//					for (ViewTag viewTag : field.getViewTags()) {
//						sb.append(viewTag.toString());
//						sb.append(", ");
//					}
//					sb.delete(sb.length() - 2, sb.length());
//					lines.add(sb.toString());
//				}
//				lines.add("\t" + field.toString() + 
//					((shortString || !field.getModifiers().contains("final")) 
//							? ";" : getFinalFieldInit(field)));
//			}
//			lines.add("");
//		}
//
//		for (JavaMethodSignature method : methods) {
//			lines.add(" /* ext: " + method.isExt() +" */ ");
//			if (method.hasViewTags()) {
//				StringBuilder sb = new StringBuilder("\t//+ ");
//				for (ViewTag viewTag : method.getViewTags()) {
//					sb.append(viewTag.toString());
//					sb.append(", ");
//				}
//				sb.delete(sb.length() - 2, sb.length());
//				lines.add(sb.toString());
//			}
//			if (shortString || !"class".equals(signature.getType())) {
//				lines.add("\t" + method.toString() + ";");
//			} else {
//				lines.add("\t" + method.toString() + " {");
//				//TODO richtigen super aufruf hinzufügen 
//				if (method.isConstructor()) {
//					lines.add("\t\tsuper();");
//				}
//				if (MPLPlugin.WRAPPER_INTERFACES) {
//					String original = "\t\t" +
//							((method.isConstructor() || method.getType().equals("void")) ? "" : "return ") + 
//							"original(";
//					for (int i = 0; i < method.getParameterTypes().size(); i++) {
//						if (i > 0) original += ", ";
//						original += "arg" + i;
//					}
//					lines.add(original + ");");
//				} else {
//					if (!method.isConstructor()) {
//						lines.add("\t\t" + getReturnStatement(method));
//					}
//				}
//				
//				lines.add("\t}");
//			}
//		}
//		lines.add("}");
//		
//		return lines;
//	}
}
