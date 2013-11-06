package br.ufal.ic.colligens.refactoring.core;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.InputStreamReader;

public class ChangeIfToIfdef {

	public void changeAll (File file) throws Exception {
		File temp = new File("temp.c");
		FileWriter fstreamWriter = new FileWriter(temp);
		BufferedWriter out = new BufferedWriter(fstreamWriter);
		
		if (!file.getName().equals("stubs.h") && !file.getName().equals("platform.h")){
			out.write("#include <stubs.h>\n\n");
		}
		
		FileInputStream fstream = new FileInputStream(file);
		// Get the object of DataInputStream
		DataInputStream in = new DataInputStream(fstream);
		BufferedReader br = new BufferedReader(new InputStreamReader(in));
		String strLine;
		//Read File Line By Line
		while ((strLine = br.readLine()) != null)   {
			String line = strLine.replace("    ", " ").replace("   ", " ").replace("  ", " ").replace("# ", "#");
			if (line.contains("#if ")){
				System.out.println("BE CAREFUL: " + line);
				if (!line.contains("defined")){
					
					System.out.println("Before: " + line);
					if (line.contains("#if !")){
						line = line.replace("#if !", "#ifndef ");
					} else {
						line = line.replace("#if ", "#ifdef ");
					}
					
					System.out.println("After: " + line);
					System.out.println();
				}
			} else if ( (line.contains("#ifdef") || line.contains("#ifndef")) && (line.contains(">") || (line.contains("<") || line.contains("=") || line.contains("!=")))){
				System.out.println("BE CAREFUL: " + line);
			}
			out.write(line + "\n");
		}
		//Close the input stream
		in.close();
		//Close the output stream
		out.close();
		
		temp.renameTo(file);
	}
	
}
