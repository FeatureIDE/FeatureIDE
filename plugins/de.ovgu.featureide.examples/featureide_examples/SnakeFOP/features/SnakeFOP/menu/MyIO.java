package menu;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;

/**
 * Speichert wichtige Informationen des Benutzers und liest sie aus.
 * 
 * @author Alexander Grebhahn
 * @author Reimar Schröter
 * 
 * @version 1.0
 */
public abstract class MyIO {
	/**
	 * Relativer Pfad zur Highscore-Datei ({@value #FILENAME_HIGHSCORE}).
	 */
	public static final String FILENAME_HIGHSCORE = "highscore.dat";
	/**
	 * Relativer Pfad zur Level-Datei ({@value}).
	 */
	public static final String FILENAME_LEVEL = "bin/level/level.dat";
	/**
	 * Relativer Pfad zur Tileset-Datei Nr.&nbsp;1 ({@value}).
	 */
	public static final String FILENAME_ENTITIES = "/picture/entity.png";
	/**
	 * Relativer Pfad zur Tileset-Datei Nr.&nbsp;2 ({@value}).
	 */
	public static final String FILENAME_ENTITIES9 = "/picture/entity9.png";

	/**
	 * Liest Daten aus einer Datei.
	 * 
	 * @param filename der Dateiname
	 * 
	 * @return alle Zeilen der Datei oder ein leeres Array, falls ein Fehler auftritt
	 * 
	 * @see #readLines(String, int)
	 */
	public static String[] readLines(String filename) {
		return readLines(filename, 10);
	}
	
	/**
	 * Liest Daten aus einer Datei.
	 * 
	 * @param filename der Dateiname
	 * @param estimatedLines die geschätze Anzahl an Zeilen in der Datei
	 * 
	 * @return alle Zeilen der Datei oder ein leeres Array, falls ein Fehler auftritt
	 * 
	 * @see #readLines(String)
	 */
	public static String[] readLines(String filename, int estimatedLines) {
		ArrayList<String> list = new ArrayList<String>(estimatedLines);
		BufferedReader reader = null;
		try {
			reader = new BufferedReader(new FileReader(filename));
			String data;
			while ((data = reader.readLine()) != null) {
				if (!data.isEmpty()) {
					list.add(data);
				}
			}
		} catch (Exception e) {
			System.err.println("Fehler beim Laden der Datei " + e.getMessage());
			return null;
		} finally {
			if (reader != null) {
				try {
					reader.close();
				} catch (IOException e) {
					System.err.println("Fehler beim Schließen der Datei " + e.getMessage());
				}
			}
		}
		String[] ret = new String[list.size()];
		list.toArray(ret);
		return ret;
	}
	
	/**
	 * Schreibt den Highscore des Benutzers.
	 * 
	 * @param filename der Dateiname
	 * @param lines der zu schreibende Text
	 */
	public static void writeLines(String filename, String lines) {
		BufferedWriter writer = null;
		try {
			writer = new BufferedWriter(new FileWriter(filename));
			writer.write(lines);
		} catch (IOException e) {
			System.err.println("Fehler beim Speichern der Datei " + e.getMessage());
		} finally {
			if (writer != null) {
				try {
					writer.close();
				} catch (IOException e) {
					System.err.println("Fehler beim Schließen der Datei " + e.getMessage());
				}
			}
		}
	}
}
