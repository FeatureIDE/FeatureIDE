/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.contracts.utils;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.StringReader;

/**
 * 
 * @author Jens Meinicke
 *
 */
public class Reader {

    /**
     * Use {@link File#getAbsolutePath()}.
     * @param filePath
     * @return
     */
	public final String getFileContent(final String filePath) {
	    final StringBuilder stringBuilder = new StringBuilder();
	    try (BufferedReader reader = new BufferedReader(new FileReader(filePath))) {
	        String line = reader.readLine();
	        while (line != null) {
	            stringBuilder.append(line);
	            stringBuilder.append("\r\n");
	            line = reader.readLine();
	        }
	    } catch (IOException e) {
			e.printStackTrace();
		}
	    return stringBuilder.toString();
	}

	/**
	 *  returns a string with (x,y) representing line number and offset of a position in a given string
     * @param originalContent the string
	 * @param index index of position in the string
	 * @return
	 */
	public static String getLineString(String originalContent, int index) {
	        originalContent = originalContent.substring(0, index);
	        StringReader reader = new StringReader(originalContent);
	        BufferedReader br = new BufferedReader(reader);

	        String last = "";

	        if (originalContent.contains("\n"))
	            last = originalContent.substring(originalContent.lastIndexOf("\n"),
	                    index);
	        int lineCount = 0;
	        String line;
	        try {
	            while ((line = br.readLine()) != null) {
	                lineCount++;
	            }
	        } catch (IOException e) {
	            e.printStackTrace();
	        }

	        return "(" + lineCount + ":" + last.length() + ")";
	    }
	
}
