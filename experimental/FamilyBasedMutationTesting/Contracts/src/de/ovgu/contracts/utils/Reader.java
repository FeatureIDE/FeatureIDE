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
