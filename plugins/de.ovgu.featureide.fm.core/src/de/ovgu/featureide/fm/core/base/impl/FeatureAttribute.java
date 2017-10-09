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
 * @author "Werner Jan"
 */
public class FeatureAttribute {

	public enum Types {
		STRING, DOUBLE, LONG, BOOLEAN
	}

	protected boolean configurable;
	protected String name;
	protected String value;
	protected String unit;
	protected boolean recursive;
	protected Types type;

	public FeatureAttribute() {
		name = "";
		type = null;
		recursive = false;
		value = "";
		unit = "";
		configurable = false;
	}
	
	public FeatureAttribute(String name, String value, String type, String unit, boolean recursive, boolean configurable) {
		this.name = name;
		this.value = value;
		this.setTypeFromString(type);
		this.unit = unit;
		this.recursive = recursive;
		this.configurable = configurable;
	}
	

	public boolean getConfigurable() {
		return configurable;
	}

	public String getName() {
		return name;
	}

	public boolean getRecursive() {
		return recursive;
	}

	public String getUnit() {
		return unit;
	}

	public Types getType() {
		return type;
	}
	
	public String getTypeString() {
		return type.toString().toLowerCase();
	}

	public String getTypeNames() {
		StringBuilder sb = new StringBuilder();
		String types = "";
		for (final Types typeNames: Types.values()) {
			sb.append(types);
			types = ", ";
			sb.append(typeNames.toString().toLowerCase());
		}
		return sb.toString();
	}

	public String getValue() {
		return value;
	}

	public void setConfigurable(boolean configurable) {
		this.configurable = configurable;
	}
	
	public void setConfigurable(String configurableString) {
		if (configurableString.isEmpty() || configurableString.toLowerCase().equals("false")) {
			this.configurable = false;
		} else if (value.toLowerCase().equals("true")){
			this.configurable = true;
		}
	}

	public void setName(String name) {
		this.name = name;
	}

	public void setRecursive(boolean recursive) {
		this.recursive = recursive;

	}

	public void setTypeFromString(String type) {
		type = type.toUpperCase();
		for (final Types typeNames : Types.values()) {
			if (typeNames.toString().equals(type)) {
				this.type = typeNames;
			}
		}
	}

	public void setType(Types type) {
		this.type = type;
	}

	public void setUnit(String unit) {
		this.unit = unit;
	}

	public void setValue(String value) {
		this.value = value;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
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
	
	public boolean checkValue() {
		if (type.toString().equals("LONG")) {
			try {
				Long.parseLong(value);
			} catch (NumberFormatException e) {
				return false;
			}
		}
		if (type.toString().equals("DOUBLE")) {
			try {
				Double.parseDouble(value);
			} catch (NumberFormatException e) {
				return false;
			}
		}
		if (type.toString().equals("BOOLEAN")) {
			if (value.toLowerCase().equals("true") || value.toLowerCase().equals("false")) {
				return true;
			}
		}
		return true;
	}
	
	public boolean checkValue(String value) {
		if (type.toString().equals("LONG")) {
			try {
				Long.parseLong(value);
			} catch (NumberFormatException e) {
				return false;
			}
		}
		if (type.toString().equals("DOUBLE")) {
			try {
				Double.parseDouble(value);
			} catch (NumberFormatException e) {
				return false;
			}
		}
		if (type.toString().equals("BOOLEAN")) {
			if (type.toString().toLowerCase().equals("true") || type.toString().toLowerCase().equals("false")) {
				return true;
			}
		}
		return true;
	}
	
}
