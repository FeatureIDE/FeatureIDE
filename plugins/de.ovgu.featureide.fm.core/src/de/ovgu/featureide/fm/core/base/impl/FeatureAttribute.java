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
package de.ovgu.featureide.fm.core.base.impl;

/**
 * Attributes for Features.
 *
 * @author "Daniel Marcel"
 * @author "Werner Jan"
 */
public class FeatureAttribute {

	static final String STRING = "STRING";
	static final String DOUBLE = "DOUBLE";
	static final String LONG = "LONG";
	static final String BOOLEAN = "BOOLEAN";

	/**
	 * Allowed types for FeatureAttributes.
	 *
	 * @author "Werner Jan"
	 */
	private enum Types {
		STRING, DOUBLE, LONG, BOOLEAN
	}

	private boolean configurable;
	private String name;
	private String value;
	private String unit;
	private boolean recursive;
	private Types type;

	/**
	 * Create empty FeatureAttribute.
	 */
	public FeatureAttribute() {
		name = "";
		type = null;
		recursive = false;
		value = "";
		unit = "";
		configurable = false;
	}

	/**
	 * @param name Name
	 * @param value Value
	 * @param type Type
	 * @param unit Unit
	 * @param recursive recursive
	 * @param configurable configurable
	 */
	public FeatureAttribute(String name, String value, String type, String unit, boolean recursive, boolean configurable) {
		this.name = name;
		this.value = value;
		setTypeFromString(type);
		this.unit = unit;
		this.recursive = recursive;
		this.configurable = configurable;
	}

	/**
	 * @return True, if the value of this FeatureAttribute matches its type. Else false.
	 */
	public boolean checkValue() {
		if (type.toString().equals(LONG)) {
			try {
				Long.parseLong(value);
				return true;
			} catch (final NumberFormatException e) {
				return false;
			}
		}
		if (type.toString().equals(DOUBLE)) {
			try {
				Double.parseDouble(value);
				return true;
			} catch (final NumberFormatException e) {
				return false;
			}
		}
		if (type.toString().equals(BOOLEAN)) {
			if (value.toLowerCase().equals("true") || value.toLowerCase().equals("false")) {
				return true;
			}
		}
		return true;
	}

	/**
	 * @param Check if the String value matches the defined type.
	 * @return true if match, else false.
	 */
	public boolean checkValue(String value) {
		if (type.toString().equals(LONG)) {
			try {
				Long.parseLong(value);
				return true;
			} catch (final NumberFormatException e) {
				return false;
			}
		}
		if (type.toString().equals(DOUBLE)) {
			try {
				Double.parseDouble(value);
				return true;
			} catch (final NumberFormatException e) {
				return false;
			}
		}
		if (type.toString().equals(BOOLEAN)) {
			if (value.toLowerCase().equals("true") || value.toLowerCase().equals("false")) {
				return true;
			} else {
				return false;
			}
		}
		return true;
	}

	/**
	 * @return Object of the defined type.
	 */
	public Object getValueObject() {
		if (type.toString().equals(LONG)) {
			return Long.parseLong(value);
		}
		if (type.toString().equals(DOUBLE)) {
			return Double.parseDouble(value);
		}
		if (type.toString().equals(BOOLEAN)) {
			return value.toLowerCase().equals("true");
		}
		return value;
	}

	/**
	 * @return boolean value of configurable.
	 */
	public boolean getConfigurable() {
		return configurable;
	}

	/**
	 * @return String value of name.
	 */
	public String getName() {
		return name;
	}

	/**
	 * @return boolean value of recursive.
	 */
	public boolean getRecursive() {
		return recursive;
	}

	/**
	 * @return type enum.
	 */
	public Types getType() {
		return type;
	}

	/**
	 * @return Concatenation of the allowed Types. Separated through comma.
	 */
	public String getTypeNames() {
		final StringBuilder sb = new StringBuilder();
		String types = "";
		for (final Types typeNames : Types.values()) {
			sb.append(types);
			types = ", ";
			sb.append(typeNames.toString().toLowerCase());
		}
		return sb.toString();
	}

	/**
	 * @return Type as string in lower case.
	 */
	public String getTypeString() {
		return type.toString().toLowerCase();
	}

	/**
	 * @return Unit.
	 */
	public String getUnit() {
		return unit;
	}

	/**
	 * @return Value.
	 */
	public String getValue() {
		return value;
	}

	/**
	 * @param Set configurable with a boolean value.
	 */
	public void setConfigurable(boolean configurable) {
		this.configurable = configurable;
	}

	/**
	 * @param Setting boolean value of configurable if the string is true or false.
	 */
	public void setConfigurable(String configurableString) {
		if (configurableString.isEmpty() || configurableString.toLowerCase().equals("false")) {
			configurable = false;
		} else if (value.toLowerCase().equals("true")) {
			configurable = true;
		}
	}

	/**
	 * @param Setting name from string.
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * @param Set recursive from boolean.
	 */
	public void setRecursive(boolean recursive) {
		this.recursive = recursive;

	}

	/**
	 * @param Setting the type from a string, if the String is in the allowed.
	 */
	public void setTypeFromString(String type) {
		type = type.toUpperCase();
		for (final Types typeNames : Types.values()) {
			if (typeNames.toString().equals(type)) {
				this.type = typeNames;
			}
		}
	}

	/**
	 * @param type set Type from given type.
	 */
	public void setType(Types type) {
		this.type = type;
	}

	/**
	 * @param Set unit from String.
	 */
	public void setUnit(String unit) {
		this.unit = unit;
	}

	/**
	 * @param Set value from String.
	 */
	public void setValue(String value) {
		this.value = value;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(name + ": \n");
		if (!value.isEmpty()) {
			sb.append(" -" + "value: " + value);
		}
		if (!unit.isEmpty()) {
			sb.append(" -" + "unit: " + unit);
		}
		if (recursive) {
			sb.append(" -" + "recursive: true");
		}
		if (configurable) {
			sb.append(" -" + "configurable: true");
		}
		return sb.toString();
	}

}
