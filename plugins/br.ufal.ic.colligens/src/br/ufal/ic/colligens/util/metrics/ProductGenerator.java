package br.ufal.ic.colligens.util.metrics;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

public class ProductGenerator {

	// Check for soundness percent of possible products.
	private static final double SOUNDNESS = 0.1;

	public static boolean isValidJavaIdentifier(String s) {
		// An empty or null string cannot be a valid identifier
		if ((s == null) || (s.length() == 0)) {
			return false;
		}

		final char[] c = s.toCharArray();
		if (!Character.isJavaIdentifierStart(c[0])) {
			return false;
		}

		for (int i = 1; i < c.length; i++) {
			if (!Character.isJavaIdentifierPart(c[i])) {
				return false;
			}
		}

		return true;
	}

	// It returns a set with all different directives.
	public Set<String> getDirectives(File file) throws Exception {
		final Set<String> directives = new HashSet<String>();

		final FileInputStream fstream = new FileInputStream(file);
		final DataInputStream in = new DataInputStream(fstream);
		final BufferedReader br = new BufferedReader(new InputStreamReader(in));
		String strLine;

		while ((strLine = br.readLine()) != null) {

			strLine = strLine.trim();

			if (strLine.startsWith("#if") || strLine.startsWith("#elif")) {

				strLine = strLine.replaceAll("(?:/\\*(?:[^*]|(?:\\*+[^*/]))*\\*+/)|(?://.*)", "");

				String directive = strLine.replace("#ifdef", "").replace("#ifndef", "").replace("#if", "");
				directive = directive.replace("defined", "").replace("(", "").replace(")", "");
				directive = directive.replace("||", "").replace("&&", "").replace("!", "").replace("<", "").replace(">", "").replace("=", "");

				final String[] directivesStr = directive.split(" ");

				for (int i = 0; i < directivesStr.length; i++) {
					if (!directivesStr[i].trim().equals("") && ProductGenerator.isValidJavaIdentifier(directivesStr[i].trim())) {
						directives.add(directivesStr[i].trim());
					}
				}
			}
		}
		in.close();
		return directives;
	}

	// It generates combinatorial for each possible product.
	public <T> Set<Set<T>> powerSet(Set<T> originalSet) {
		final Set<Set<T>> sets = new HashSet<Set<T>>();
		if (originalSet.isEmpty()) {
			sets.add(new HashSet<T>());
			return sets;
		}
		final List<T> list = new ArrayList<T>(originalSet);
		final T head = list.get(0);
		final Set<T> rest = new HashSet<T>(list.subList(1, list.size()));
		for (final Set<T> set : powerSet(rest)) {
			final Set<T> newSet = new HashSet<T>();
			newSet.add(head);
			newSet.addAll(set);
			sets.add(newSet);
			sets.add(set);
		}
		return sets;
	}

	// It executes external commands.
	public String runCommand(String cmd) {
		String result = "";
		try {
			final Runtime rt = Runtime.getRuntime();
			final Process pr = rt.exec(cmd);

			final BufferedReader input = new BufferedReader(new InputStreamReader(pr.getInputStream()));

			String line = null;

			while ((line = input.readLine()) != null) {
				result += line + "\n";
			}

			final int exitVal = pr.waitFor();
			if (exitVal != 0) {
				System.out.println("Problem running external command!");
			}

		} catch (final Exception e) {
			System.out.println(e.toString());
			e.printStackTrace();
		}
		return result;
	}

	// It saves a String to a file, replacing the file's contents.
	public void saveToFile(String filePath, String textToSave) {
		final File file = new File(filePath);
		if (file.exists()) {
			file.delete();
		}
		try {
			final BufferedWriter out = new BufferedWriter(new FileWriter(file));
			out.write(textToSave);
			out.close();
		} catch (final IOException e) {
			e.printStackTrace();
		}
	}

	// It generates each possible product.
	public void generateProducts(String originalFile) throws Exception {
		final Set<String> directives = getDirectives(new File(originalFile));

		// Generating all possible products.
		final Set<Set<String>> sets = this.powerSet(directives);

		int count = 1;

		for (final Iterator<Set<String>> i = sets.iterator(); i.hasNext();) {
			final Set<String> set = i.next();

			String cmd = "gcc -P -E ";

			for (final Iterator<String> j = set.iterator(); j.hasNext();) {
				final String directive = j.next();
				cmd += " -D " + directive + " ";
			}
			cmd += originalFile;

			final String code = runCommand(cmd);
			saveToFile(originalFile.replace("original.c", "") + "test" + count + ".c", code);
			count++;

			if ((directives.size() > 5) && (directives.size() <= 10)) {
				// Define soundness to set the percentage of product to analyze.
				if (count >= (sets.size() * ProductGenerator.SOUNDNESS)) {
					break;
				}
			} else if (directives.size() > 10) {
				break;
			}

		}
	}

}
