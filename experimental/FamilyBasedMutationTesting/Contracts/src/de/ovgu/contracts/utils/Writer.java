package de.ovgu.contracts.utils;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;

/**
 * 
 * @author Jens Meinicke
 *
 */
public final class Writer {
    
    private Writer() { }

	public static void setFileContent(final String filePath, final String content) {
		setFileContent(new File(filePath), content);
	}
	
	public static void setFileContent(final File file, final String content) {
		FileManager.createFile(file);
		try (PrintWriter writer = new PrintWriter(file, "UTF-8");) {
			writer.println(content);
		} catch (FileNotFoundException | UnsupportedEncodingException e) {
			e.printStackTrace();
		}
	}
}
