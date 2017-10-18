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
package de.ovgu.featureide.featurehouse.signature.fuji;

import static de.ovgu.featureide.fm.core.localization.StringTable.EXTENDS;
import static de.ovgu.featureide.fm.core.localization.StringTable.IMPLEMENTS;

import de.ovgu.featureide.core.signature.base.AbstractClassFragment;
import de.ovgu.featureide.core.signature.base.AbstractFieldSignature;
import de.ovgu.featureide.core.signature.base.AbstractMethodSignature;
import de.ovgu.featureide.core.signature.base.AbstractSignature;

public class FujiStringBuilder {

	private static final String LINE_SEPARATOR = System.getProperty("line.separator");

	public static String getClassString(AbstractClassFragment cls, boolean shortString) {
		final StringBuilder sb = new StringBuilder();

		if (cls.getSignature().getParent() == null) {
			if (!cls.getSignature().getPackage().isEmpty()) {
				sb.append("package ");
				sb.append(cls.getSignature().getPackage());
				sb.append(';');
				sb.append(LINE_SEPARATOR);
			}

			if (!cls.getSignature().getImportList().isEmpty()) {
				for (final String importClass : cls.getSignature().getImportList()) {
					sb.append(importClass);
					sb.append(LINE_SEPARATOR);
				}
				sb.append(LINE_SEPARATOR);
			}
		}

		sb.append(cls.getSignature().toString());

		if (!cls.getSignature().getExtendList().isEmpty()) {
			if (shortString) {
				sb.append(LINE_SEPARATOR);
				sb.append("\t\textends ");
			} else {
				sb.append(EXTENDS);
			}
			for (final String ext : cls.getSignature().getExtendList()) {
				sb.append(ext);
				sb.append(", ");
			}
			sb.delete(sb.length() - 2, sb.length());
		}

		if (!cls.getSignature().getImplementList().isEmpty()) {
			if (shortString) {
				sb.append(LINE_SEPARATOR);
				sb.append("\t\timplements ");
			} else {
				sb.append(IMPLEMENTS);
			}
			for (final String impl : cls.getSignature().getImplementList()) {
				sb.append(impl);
				sb.append(", ");
			}
			sb.delete(sb.length() - 2, sb.length());
		}

		sb.append(" {");
		sb.append(LINE_SEPARATOR);

		if (!cls.getInnerClasses().isEmpty()) {
			for (final AbstractClassFragment innerClass : cls.getInnerClasses().values()) {
				sb.append('\t');
				String innerClassString;
				if (shortString) {
					innerClassString = innerClass.toShortString();
				} else {
					innerClassString = innerClass.toString();
				}
				sb.append(innerClassString.replace(LINE_SEPARATOR, LINE_SEPARATOR + '\t'));
				sb.append(LINE_SEPARATOR);
			}
			sb.append(LINE_SEPARATOR);
		}

		if (!cls.getMembers().isEmpty()) {
			for (final AbstractSignature member : cls.getMembers()) {
				sb.append("\t");
				sb.append(member.toString().replace(LINE_SEPARATOR, LINE_SEPARATOR + '\t'));
				if (member instanceof AbstractFieldSignature) {
					final AbstractFieldSignature field = (AbstractFieldSignature) member;
					if (shortString || !field.isFinal()) {
						sb.append(';');
					} else {
						sb.append(getFinalFieldInit(field));
					}
				} else if (member instanceof AbstractMethodSignature) {
					final AbstractMethodSignature method = (AbstractMethodSignature) member;
					if (shortString || !"class".equals(cls.getSignature().getType())) {
						sb.append(';');
					} else {
						sb.append(" {");
						sb.append(LINE_SEPARATOR);

						// TODO MPL: use Fuji
						if (method.isConstructor()) {
							sb.append("\t\tsuper();");
						}
						if (!method.isConstructor()) {
							sb.append("\t\t" + getReturnStatement(method));
						}

						sb.append(LINE_SEPARATOR);
						sb.append("\t}");
					}
				}
				sb.append(LINE_SEPARATOR);
			}
			sb.append(LINE_SEPARATOR);
		}
		sb.append(LINE_SEPARATOR);
		sb.append('}');

		return sb.toString();
	}

	private static String getFinalFieldInit(AbstractFieldSignature field) {
		return " = " + getTypeDefaultValue(field);
	}

	private static String getReturnStatement(AbstractMethodSignature method) {
		return "return " + getTypeDefaultValue(method);
	}

	private static String getTypeDefaultValue(AbstractSignature element) {
		final String type = element.getType();
		if (type.equals("void")) {
			return ";";
		} else if (type.equals("boolean")) {
			return "true;";
		} else if (type.equals("int") || type.equals("double") || type.equals("char") || type.equals("long") || type.equals("float") || type.equals("byte")
			|| type.equals("short")) {
			return "0;";
		} else {
			return "null;";
		}
	}
}
