package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import static org.junit.Assert.*;

import java.io.BufferedReader;
import java.io.StringReader;

import org.junit.Test;

public class DirectivesNodeTest {

	DirectivesNode node = new DirectivesNode();
	
	String fileContent = "public class Main {\n"+
"\n" + 
"	public static void main(String[] args){\n" +
"		//#if Hello\n" +
"		System.out.print(\"Hello\");\n" + 
"		//#endif\n" +
"		//#if Beautiful && Hello\n" +
"		System.out.print(\" beautiful\");\n" +
"		//#endif\n" +
"		//#if Wonderful\n" +
"//@		System.out.print(\" wonderful\");\n" +	
"		//#endif\n" +
"		//#if World\n" +
"		/*\n" +
"		System.out.print(\" world!\");\n" +
"		*/ System.out.println(\"bla\");\n" +
"		//#endif\n" +
"		\n" +
"		\n" +
"	}\n" +
"}";
	
	@Test
	public void testName() throws Exception {
		String featureName = "Hello";
		StringReader stringReader = new StringReader(fileContent);
		node.checkContent(featureName, new BufferedReader(stringReader));
		
		
		System.out.println(node.featuresAndLines);
		
		assertEquals(Integer.valueOf(1), node.featuresAndLines.get(featureName));
	}
	
}
