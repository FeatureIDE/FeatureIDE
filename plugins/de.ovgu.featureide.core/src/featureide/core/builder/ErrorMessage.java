/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.core.builder;

/**
 * for encapsulating the error message that is displayed in the problems view
 * 
 * @author Janet Feigenspan
 * @deprecated
 */
public class ErrorMessage {

	private String type;
	private String message;
	private String file;
	private int line;
	
	public ErrorMessage() {}
	public ErrorMessage(String type, String message, String file, int line) {
		this.type = type;
		this.message = message;
		this.file = file;
		this.line = line;
	}
	
	public void setFile(String string) {
		this.file = string;
	}
	public String getFile() {
		return file;
	}
	public void setLine(int line) {
		this.line = line;
	}
	public int getLine() {
		return line;
	}
	public void setMessage(String message) {
		this.message = message;
	}
	public String getMessage() {
		return message;
	}
	public void setType(String type) {
		this.type = type;
	}
	public String getType() {
		return type;
	}
	
	public String toString() {
		return "Type: " + type + "\n Message: " + message + "\n File: " + file + "\n Line: " + line;
	}
}
