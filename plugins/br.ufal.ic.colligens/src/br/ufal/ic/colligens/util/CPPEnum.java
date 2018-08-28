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
package br.ufal.ic.colligens.util;

import java.util.ArrayList;
import java.util.List;

/**
 * Enums all Colligen CPP directives so that Eclipse can autocomplete them.
 *
 * @author Mohammed Khaled
 * @author Iris-Maria Banciu
 */
public enum CPPEnum {
	IFDEF("ifdef"), IFNOTDEF("ifndef"), ELSE("else"), END("endif"), DEFINE("define"), UNDEFINE("undefine"), IF("if");

	private String text;

	CPPEnum(String text) {
		this.text = text;
	}

	public String getText() {
		return text;
	}

	public static List<String> getAllDirectives() {
		final List<String> list = new ArrayList<String>();
		for (final CPPEnum d : CPPEnum.values()) {
			list.add(d.text + " ");
		}
		return list;
	}
}
