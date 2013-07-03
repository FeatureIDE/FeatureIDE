package br.ufal.ic.colligens.util.metrics;


import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class FindConditionalDirectives {

	private List<String> directives = new ArrayList<String>();
	private int files = 0;
	private int fileNoDirectives = 0;
	
	public void getFiles(final File folder) throws IOException {
	    for (final File fileEntry : folder.listFiles()) {
	        if (fileEntry.isDirectory()) {
	        	getFiles(fileEntry);
	        } else {
	        	if (fileEntry.getName().endsWith(".c")){
	        		this.readFile(fileEntry);
	        	}
	        }
	    }
	}
	
	public void readFile(File file) throws IOException{
		boolean directives = false;
		files++;
		
		FileInputStream fstream = new FileInputStream(file);
		DataInputStream in = new DataInputStream(fstream);
		BufferedReader br = new BufferedReader(new InputStreamReader(in));
		String strLine;
		while ((strLine = br.readLine()) != null){
			if (strLine.contains("#if") || strLine.contains("#elif")){
				
				directives = true;
				
				String pattern = "(?://.*)|(/\\*(?:.|[\\n\\r])*?\\*/)";
				Pattern r = Pattern.compile(pattern);

				// Now create matcher object.
				Matcher m = r.matcher(strLine);
				if (m.find( )) {
					strLine = strLine.replace(m.group(), "");
				}
				
				if (!this.directives.contains(strLine.trim())){
					this.directives.add( (strLine.trim()) );
				}
			}
		}
		
		if (!directives){
			fileNoDirectives++;
		}
		
		in.close();
	}
	
	public static void main(String[] args) throws IOException {
		FindConditionalDirectives findConditionalDirectives = new FindConditionalDirectives();
		findConditionalDirectives.getFiles(new File("projects/lighttpd/src"));
		List<String> directives = findConditionalDirectives.directives;
		
		for (int i = 0; i < directives.size(); i++){
			System.out.println(directives.get(i));
		}
		
		System.out.println("Size: " + directives.size());
		System.out.println("Files: " + findConditionalDirectives.files);
		System.out.println("No Directives: " + findConditionalDirectives.fileNoDirectives);
	}
	
}
