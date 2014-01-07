package br.ufal.ic.colligens.refactoring.core;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;

public class CountDirectives {
	
	int count = 0;
	int nfiles = 0;
	
	public static void main(String[] args) throws IOException {
		CountDirectives c = new CountDirectives();
		c.listFiles(new File("directives/flex-2.5.37"));
		
		System.out.println("Number of files: " + c.nfiles);
		System.out.println("Number of directives: " + c.count);
	}
	
	public void countDirectives (File file) throws IOException {
		FileInputStream fstream = new FileInputStream(file);
		
		DataInputStream in = new DataInputStream(fstream);
		BufferedReader br = new BufferedReader(new InputStreamReader(in));
		String strLine;
		
		int print = 0;
		
		while ((strLine = br.readLine()) != null)   {
			if (strLine.trim().startsWith("#if") || strLine.trim().startsWith("#else") || strLine.trim().startsWith("#elif")){
				print++;
				count++;
			}
			if (strLine.trim().startsWith("#endif")){
				print--;
			}
			if (print > 0){
				System.out.println(strLine);
			}
		}
		  
		br.close();
		in.close();
	}
	
	public void listFiles (File path) throws IOException{
		File[] files = path.listFiles();
		for (File file : files){
			if (file.isDirectory()){
				this.listFiles(file);
			} else {
				if (file.getName().endsWith(".c") || file.getName().endsWith(".h")){
					nfiles++;
					//if (file.getName().equals("scan.c")){
						this.countDirectives(file);
					//}
				}
			}
		}
	}
}
