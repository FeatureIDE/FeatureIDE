/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.featurehouse.FSTParser;

/**
 * Single token: method or field
 * 
 * @author Dariusz Krolikowski
 */
public class JavaToken {

	private boolean _abstract = false;
	private boolean _final = false;
	private boolean _native = false;
	private boolean _private = false;
	private boolean _protected = false;
	private boolean _public = false;
	private boolean _strictfp = false;
	private boolean _static = false;
	private boolean _synchronized = false;
	private boolean _transient = false;
	private boolean _volatile = false;
	
	private boolean isField;
	private String type;
	private String args;
	private String name;
	
	public JavaToken(String name, String args, boolean isField){
		this.name = name;
		this.args = args;
		this.isField = isField;
	}
	
	public String toString(){
		String res = "";
		res += "Field: " + isField + "\n";
		res += "Type: " + type + "\n";
		res += "Name: " + name + "\n";
		if (!isField)
			res += "Arguments: " + args + "\n";
		
		res += "Modifier: ";
		if (_abstract)
			res += "abstract ";
		if (_final)
			res += "final ";
		if (_native)
			res += "native ";
		if (_private)
			res += "private ";
		if (_protected)
			res += "protected ";
		if (_public)
			res += "public ";
		if (_strictfp)
			res += "strictfp ";
		if (_static)
			res += "static ";
		if (_synchronized)
			res += "synchronized ";
		if (_transient)
			res += "transient ";
		if (_volatile)
			res += "volatile ";
		res += "\n";
		
		return res;
	}
	
	/**
	 * @return the _abstract
	 */
	public boolean is_abstract() {
		return _abstract;
	}
	/**
	 * @param _abstract the _abstract to set
	 */
	public void set_abstract(boolean _abstract) {
		this._abstract = _abstract;
	}
	/**
	 * @return the _final
	 */
	public boolean is_final() {
		return _final;
	}
	/**
	 * @param _final the _final to set
	 */
	public void set_final(boolean _final) {
		this._final = _final;
	}
	/**
	 * @return the _native
	 */
	public boolean is_native() {
		return _native;
	}
	/**
	 * @param _native the _native to set
	 */
	public void set_native(boolean _native) {
		this._native = _native;
	}
	/**
	 * @return the _private
	 */
	public boolean is_private() {
		return _private;
	}
	/**
	 * @param _private the _private to set
	 */
	public void set_private(boolean _private) {
		this._private = _private;
	}
	/**
	 * @return the _protected
	 */
	public boolean is_protected() {
		return _protected;
	}
	/**
	 * @param _protected the _protected to set
	 */
	public void set_protected(boolean _protected) {
		this._protected = _protected;
	}
	/**
	 * @return the _public
	 */
	public boolean is_public() {
		return _public;
	}
	/**
	 * @param _public the _public to set
	 */
	public void set_public(boolean _public) {
		this._public = _public;
	}
	/**
	 * @return the _strictfp
	 */
	public boolean is_strictfp() {
		return _strictfp;
	}
	/**
	 * @param _strictfp the _strictfp to set
	 */
	public void set_strictfp(boolean _strictfp) {
		this._strictfp = _strictfp;
	}
	/**
	 * @return the _static
	 */
	public boolean is_static() {
		return _static;
	}
	/**
	 * @param _static the _static to set
	 */
	public void set_static(boolean _static) {
		this._static = _static;
	}
	/**
	 * @return the _synchronized
	 */
	public boolean is_synchronized() {
		return _synchronized;
	}
	/**
	 * @param _synchronized the _synchronized to set
	 */
	public void set_synchronized(boolean _synchronized) {
		this._synchronized = _synchronized;
	}
	/**
	 * @return the _transient
	 */
	public boolean is_transient() {
		return _transient;
	}
	/**
	 * @param _transient the _transient to set
	 */
	public void set_transient(boolean _transient) {
		this._transient = _transient;
	}
	/**
	 * @return the _volatile
	 */
	public boolean is_volatile() {
		return _volatile;
	}
	/**
	 * @param _volatile the _volatile to set
	 */
	public void set_volatile(boolean _volatile) {
		this._volatile = _volatile;
	}


	
	/**
	 * @return the type
	 */
	public String getType() {
		return type;
	}

	/**
	 * @param type the type to set
	 */
	public void setType(String type) {
		this.type = type;
	}

	/**
	 * @return the args
	 */
	public String getArgs() {
		return args;
	}

	/**
	 * @param args the args to set
	 */
	public void setArgs(String args) {
		this.args = args;
	}

	/**
	 * @return the isField
	 */
	public boolean isField() {
		return isField;
	}

	/**
	 * @param isField the isField to set
	 */
	public void setField(boolean isField) {
		this.isField = isField;
	}

	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}

	/**
	 * @param name the name to set
	 */
	public void setName(String name) {
		this.name = name;
	}

}