package br.ufal.ic.colligens.refactoring.core;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;

public class OrganizeCode {

	public String removeParts(String text){
		text = text.replace("   ", " ").replace("  ", " ").replace("=", " = ").replace("=(", "= (");
		text = text.replace(" )", ")").replace("! =", "!=").replace("  ", " ").replace("= =", "==");
		text = text.replace(" [", "[").replace(" ]", "]").replace(",}", "}").replace(", }", "}").replace(" ]", "]");
		text = text.replace("=[", "= [").replace(")||", ") ||").replace("( ", "(").replace(" }", "}");
		text = text.replace(")+", ") +").replace(")-", ") -").replace(")*", ") *").replace(")/", ") /");
		return text;
	}
	
	public void organize() throws IOException {
		File file = new File("output.temp");
		FileWriter fstreamRead = new FileWriter(file);
		  BufferedWriter out = new BufferedWriter(fstreamRead);
		
		FileInputStream fstream = new FileInputStream("output.c");
		  // Get the object of DataInputStream
		  DataInputStream in = new DataInputStream(fstream);
		  BufferedReader br = new BufferedReader(new InputStreamReader(in));
		  String strLine;
		  //Read File Line By Line
		  while ((strLine = br.readLine()) != null)   {
			  // Print the content on the console
			  String line = this.removeParts(strLine) + "\n";
			 
			  if (!line.trim().equals("")){
				  out.write(line);
			  } else {
				  String next = br.readLine();
				  if (next != null){
					  next = this.removeParts(next);
					  if (next != null){
						  if (next.trim().equals("#endif") || next.trim().equals("") || next.trim().startsWith("return")){
							  out.write(next + "\n");
						  } else {
							  out.write(line);
							  out.write(next + "\n");
						  }
					  }
				  }
			  }
		  }
		  //Close the input stream
		  in.close();
		  out.close();
		  
		  file.renameTo(new File("output.c"));
	}
	public void organize(String filePath) throws IOException {
		File file = new File(System.getProperty("java.io.tmpdir")+"/output.temp");
		
		file.createNewFile();
		
		FileWriter fstreamRead = new FileWriter(file);
		BufferedWriter out = new BufferedWriter(fstreamRead);

		FileInputStream fstream = new FileInputStream(filePath);
		// Get the object of DataInputStream
		DataInputStream in = new DataInputStream(fstream);
		BufferedReader br = new BufferedReader(new InputStreamReader(in));
		String strLine;
		// Read File Line By Line
		while ((strLine = br.readLine()) != null) {
			// Print the content on the console
			String line = this.removeParts(strLine) + "\n";

			if (!line.trim().equals("")) {
				out.write(line);
			} else {
				String next = br.readLine();
				if (next != null) {
					next = this.removeParts(next);
					if (next != null) {
						if (next.trim().equals("#endif")
								|| next.trim().equals("")
								|| next.trim().startsWith("return")) {
							out.write(next + "\n");
						} else {
							out.write(line);
							out.write(next + "\n");
						}
					}
				}
			}
		}
		// Close the input stream
		in.close();
		out.close();

		file.renameTo(new File(filePath));
	}

	
}

