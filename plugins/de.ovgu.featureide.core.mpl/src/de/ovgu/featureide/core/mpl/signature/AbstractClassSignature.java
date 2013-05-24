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
package de.ovgu.featureide.core.mpl.signature;

import java.util.Collection;
import java.util.LinkedList;
import java.util.Map;

import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.signature.java.JavaFieldSignature;
import de.ovgu.featureide.core.mpl.signature.java.JavaMethodSignature;

/**
 * Abstract signature for one class.
 * 
 * @author Sebastian Krieter
 */
public abstract class AbstractClassSignature<E extends AbstractClassSignature<E>> extends AbstractSignature {

	protected String pckg;

	protected Collection<JavaFieldSignature> fields;
	protected Collection<JavaMethodSignature> methods;
	protected Map<String, E> innerClasses;
	protected Collection<String> importList, extendList, implementList;
	
	protected AbstractClassSignature(String name, String modifiers, String type, String pckg, LinkedList<ViewTag> viewTags, boolean ext) {
		super(name, modifiers, type, viewTags, ext);
		if (pckg == null) {
			this.pckg = "";
		} else {
			this.pckg = pckg;
		}
	}
	
	protected AbstractClassSignature(String name, String modifiers, String type, String pckg, boolean ext) {
		this(name, modifiers, type, pckg, null, ext);
	}
	
	public String getFullName() {
		return (pckg.isEmpty()) ? '.' + name : pckg + '.' + name;
	}

	public String getPackage() {
		return pckg;
	}

	public Collection<JavaFieldSignature> getFields() {
		return fields;
	}

	public Collection<JavaMethodSignature> getMethods() {
		return methods;
	}
	
	public Map<String, E> getInnerClasses() {
		return innerClasses;
	}

	public int getMemberCount() {
		int innerMembers = 0;
		for (E innerClass : innerClasses.values()) {
			innerMembers += innerClass.getMemberCount();
		}
		return fields.size() + methods.size() + innerClasses.size()
				+ innerMembers;
	}

	public void addField(JavaFieldSignature field) {
		fields.add(field);
	}

	public void addMethod(JavaMethodSignature method) {
		methods.add(method);
	}

	public void addInnerClass(E innerClass) {
		E orgInnerClass = innerClasses.get(innerClass.getFullName());
		if (orgInnerClass == null) {
			innerClasses.put(innerClass.getFullName(), innerClass);
		} else {
			for (String extend : innerClass.extendList) {
				orgInnerClass.addExtend(extend);
			}
			for (String implement : innerClass.implementList) {
				orgInnerClass.addImplement(implement);
			}
			for (JavaFieldSignature field : innerClass.fields) {
				orgInnerClass.addField(field);
			}
			for (JavaMethodSignature method : innerClass.methods) {
				orgInnerClass.addMethod(method);
			}
			for (E innerInnerClass : innerClass.innerClasses.values()) {
				orgInnerClass.addInnerClass(innerInnerClass);
			}
		}
	}

	public void addImport(String imp) {
		importList.add(imp);
	}

	public void addImplement(String implement) {
		implementList.add(implement);
	}

	public void addExtend(String extend) {
		extendList.add(extend);
	}
	
	@Deprecated
	public  void addDefaultViewTag(ViewTag classViewTag, ViewTag methodViewTag, ViewTag fieldViewTag) {
		this.addViewTag(classViewTag);
		for (E innerClass : innerClasses.values()) {
			innerClass.addDefaultViewTag(classViewTag, methodViewTag, fieldViewTag);
		}
		for (JavaMethodSignature method : methods) {
			method.addViewTag(methodViewTag);
		}
		for (JavaFieldSignature field : fields) {
			field.addViewTag(fieldViewTag);
		}
	}
	
	public void deleteViewTag(String name) {
		super.deleteViewTag(name);
		for (E innerClass : innerClasses.values()) {
			innerClass.deleteViewTag(name);
		}
		for (JavaMethodSignature method : methods) {
			method.deleteViewTag(name);
		}
		for (JavaFieldSignature field : fields) {
			field.deleteViewTag(name);
		}
	}
	
	@Override
	public String toString() {
		return toString(false, false);
	}

	public String toShortString() {
		return toString(true, true);
	}
	
	private String toString(boolean shortString, boolean exampleViewTags) {
		final StringBuilder sb = new StringBuilder();
		for (String line : getLines(shortString)) {
			sb.append(line);
			sb.append(LINE_SEPARATOR);
		}
		return sb.toString();
	}
	
	private LinkedList<String> getLines(boolean shortString) {
		final LinkedList<String> lines = new LinkedList<String>();
		
		if (!pckg.isEmpty()) {
			lines.add("package " + pckg + ";");
		}
		if (!importList.isEmpty()) {
			for (String importClass : importList) {
				lines.add(importClass);
			}
			lines.add("");
		}
		
		lines.add("/* ext: " + ext +" */");
		
		if (!viewTags.isEmpty()) {
			StringBuilder sb = new StringBuilder("//+ ");
			for (ViewTag viewTag : viewTags) {
				sb.append(viewTag.toString());
				sb.append(", ");
			}
			sb.delete(sb.length() - 2, sb.length());
			lines.add(sb.toString());
		}
		lines.add(modifiers + " " + type + " " + name);

		if (!extendList.isEmpty()) {
			String extend = (shortString) ? "\t\textends " : " extends ";
			for (String ext : extendList) {
				extend += ext + ",";
			}
			lines.add(extend.substring(0, extend.length() - 1));
		}

		if (!implementList.isEmpty()) {
			String implement = (shortString) ? "\t\timplements " : " implements ";
			for (String impl : implementList) {
				implement += impl + ",";
			}
			lines.add(implement.substring(0, implement.length() - 1));
		}
		
		lines.add("{");

		if (!innerClasses.isEmpty()) {
			for (E innerClass : innerClasses.values()) {
				final StringBuilder sb = new StringBuilder();
				for (String line : innerClass.getLines(shortString)) {
					sb.append('\t');
					sb.append(line);
					sb.append(LINE_SEPARATOR);
				}
				lines.add(sb.toString());
			}
			lines.add("");
		}

		if (!fields.isEmpty()) {
			for (JavaFieldSignature field : fields) {
				lines.add(" /* ext: " + field.ext +" */ ");
				if (!field.viewTags.isEmpty()) {
					StringBuilder sb = new StringBuilder("\t//+ ");
					for (ViewTag viewTag : field.viewTags) {
						sb.append(viewTag.toString());
						sb.append(", ");
					}
					sb.delete(sb.length() - 2, sb.length());
					lines.add(sb.toString());
				}
				lines.add("\t" + field.toString() + 
					((shortString || !field.getModifiers().contains("final")) 
							? ";" : getFinalFieldInit(field)));
			}
			lines.add("");
		}

		for (JavaMethodSignature method : methods) {
			lines.add(" /* ext: " + method.ext +" */ ");
			if (!method.viewTags.isEmpty()) {
				StringBuilder sb = new StringBuilder("\t//+ ");
				for (ViewTag viewTag : method.viewTags) {
					sb.append(viewTag.toString());
					sb.append(", ");
				}
				sb.delete(sb.length() - 2, sb.length());
				lines.add(sb.toString());
			}
			if (shortString || !"class".equals(type)) {
				lines.add("\t" + method.toString() + ";");
			} else {
				lines.add("\t" + method.toString() + " {");
				//TODO richtigen super aufruf hinzufügen 
				if (method.isConstructor()) {
					lines.add("\t\tsuper();");
				}
				if (MPLPlugin.WRAPPER_INTERFACES) {
					String original = "\t\t" +
							((method.isConstructor() || method.getType().equals("void")) ? "" : "return ") + 
							"original(";
					for (int i = 0; i < method.getParameterTypes().size(); i++) {
						if (i > 0) original += ", ";
						original += "arg" + i;
					}
					lines.add(original + ");");
				} else {
					if (!method.isConstructor()) {
						lines.add("\t\t" + getReturnStatement(method));
					}
				}
				
				lines.add("\t}");
			}
		}
		lines.add("}");
		
		return lines;
	}

	private static String getFinalFieldInit(JavaFieldSignature field) {
		return " = " + getTypeDefaultValue(field);
	}

	private static String getReturnStatement(JavaMethodSignature method) {
		return "return " + getTypeDefaultValue(method);
	}

	private static String getTypeDefaultValue(AbstractSignature element) {
		String type = element.getType();
		if (type.equals("void")) {
			return ";";
		} else if (type.equals("boolean")) {
			return "true;";
		} else if (type.equals("int") 
				|| type.equals("double") 
				|| type.equals("char")
				|| type.equals("long") 
				|| type.equals("float")  
				|| type.equals("byte")
				|| type.equals("short"))  {
			return "0;";
		} else {
			return "null;";
		}
	}
	
	@Override
	public AbstractSignature createExtendedSignature() {
		return null;
	}
}
