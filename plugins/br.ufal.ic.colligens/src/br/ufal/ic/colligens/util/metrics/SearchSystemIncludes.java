package br.ufal.ic.colligens.util.metrics;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;

public class SearchSystemIncludes {

	private final List<String> systemIncludes = new ArrayList<String>();

	public void readFile(File file) throws IOException {
		final FileInputStream fstream = new FileInputStream(file);
		final DataInputStream in = new DataInputStream(fstream);
		final BufferedReader br = new BufferedReader(new InputStreamReader(in));
		String strLine;
		while ((strLine = br.readLine()) != null) {
			if (strLine.contains("#include") && strLine.contains("<") && strLine.contains(">")) {
				if (!systemIncludes.contains(strLine.trim())) {
					systemIncludes.add(strLine.trim());
				}
			}
		}
		in.close();
	}

	public void listFilesForFolder(final File folder) throws IOException {
		for (final File fileEntry : folder.listFiles()) {
			if (fileEntry.isDirectory()) {
				listFilesForFolder(fileEntry);
			} else {
				if (fileEntry.getName().endsWith(".h") || fileEntry.getName().endsWith(".c")) {
					System.out.println(fileEntry.getName());
					// this.readFile(fileEntry);
				}
			}
		}
	}

	public int count(String path) throws IOException {
		final File file = new File(path);
		if (file.isDirectory()) {
			listFilesForFolder(file);
		} else {
			readFile(file);
		}
		return systemIncludes.size();
	}
}
