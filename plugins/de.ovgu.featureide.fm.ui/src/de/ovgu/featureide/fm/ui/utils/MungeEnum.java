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
package de.ovgu.featureide.fm.ui.utils;

import java.util.ArrayList;
import java.util.List;

/**
 * Enums all Munge directives so that Eclipse can autocomplete them.
 *
 * @author Iris-Maria Banciu
 */
public enum MungeEnum {
	IF("if"), IF_NOT("if_not"), ELSE("else"), END("end");

	private String text;

	MungeEnum(String text) {
		this.text = text;
	}

	public String getText() {
		return text;
	}

	public static List<String> getAllDirectives() {
		final List<String> list = new ArrayList<String>();
		for (final MungeEnum d : MungeEnum.values()) {
			list.add(d.text + "[]*/");
		}
		return list;
	}

	public static List<String> getAllDirectivesNames() {
		final List<String> list = new ArrayList<String>();
		for (final MungeEnum d : MungeEnum.values()) {
			list.add(d.text);
		}
		return list;
	}

	public static List<String> getEndundElseDirctivesWithFeatureName(String featureName) {
		final List<String> list = new ArrayList<String>();

		list.add(MungeEnum.ELSE.text + "[" + featureName + "]*/");
		list.add(MungeEnum.END.text + "[" + featureName + "]*/");
		return list;
	}

	public static List<String> getEndDirctivesWithFeatureName(String featureName) {
		final List<String> list = new ArrayList<String>();

		list.add(MungeEnum.END.text + "[" + featureName + "]*/");
		return list;
	}
}
