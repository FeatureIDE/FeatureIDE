package de.ovgu.featureide.oscar.IO;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.sql.Timestamp;
import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.oscar.model.Feature;
import oscar.OscarProperties;

public class ExportImport {
	
	private static final String CSV = "csv";
	private static final String XML = "xml";
	private static final String MOD = "FeatureIDE model";

	
	
	public static void export(Feature base, OscarProperties op, Map<String, Integer[]> allPropMap, String format, IProject project){
	    
		
		
		Timestamp tsmp = new Timestamp(System.currentTimeMillis());
		String fileName="";
		StringBuilder sb=null;
		Console console = new Console();
		switch (format){
			case CSV:
				fileName = project.getLocation().toOSString()+File.separator+"propertyUsageResult_"+tsmp.toString()+"."+CSV;
				sb=generateOutputCsv(op, allPropMap);
				break;
			case MOD:
				fileName = project.getLocation().toOSString()+File.separator+"propertyUsageResult_"+tsmp.toString()+"."+XML;
				sb=generateModel(base);
				break;
			default:
				sb=generateOutputCsv(op, allPropMap);
				console.writeln(sb.toString());
				return;
		}


		FileWriter fileWriter = null;
		try {
			fileWriter = new FileWriter(fileName);
			fileWriter.write(sb.toString());
			console.writeln("Result generated in: "+fileName);
		} catch (IOException e) {
			console.writeln(e.getMessage());
		}finally{			
			try {
				fileWriter.flush();
				fileWriter.close();
			} catch (IOException e) {
				console.writeln(e.getMessage());
			}
		}
		
	}
	
	
	public static StringBuilder generateOutputCsv (OscarProperties op, Map<String, Integer[]> allPropMap){
		
		StringBuilder sb = new StringBuilder ();
		sb.append("Property, Num Usages, Num Boolean Usages, %Boolean, Known Property, Is Set\r");
		for (String s : allPropMap.keySet()) {
			Boolean knownProperty = false;
			Boolean isSet = false;
			if (op.hasProperty(s)) {
				knownProperty = true;
				isSet = op.isPropertyActive(s);
			}
				
			sb.append("" + s + "," + allPropMap.get(s)[0] + "," + allPropMap.get(s)[1]);
			if (allPropMap.get(s)[0] > 0) {
				sb.append("," + 100 * allPropMap.get(s)[1] / (allPropMap.get(s)[0]));
			} else {
				sb.append(",");
			}
			if (knownProperty) {
				sb.append("," + knownProperty + "," + isSet+"\r");
			} else {
				sb.append("," + knownProperty + ","+"\r");
			}

		}
		
		return sb;
	}
	
	public static StringBuilder generateModel (Feature base){
		StringBuilder sb = new StringBuilder ();
		sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\r");
		sb.append("<featureModel>\r");
		sb.append("<properties/>\r");
		sb.append("<struct>\r");
		sb.append(base.toString());
		sb.append("</struct>\r"
				+ "<constraints/>\r"
				+ "<calculations Auto=\"true\" Constraints=\"true\" Features=\"true\" "
				+ "Redundant=\"true\" Tautology=\"true\"/>\r"
				+ "<comments/>\r"
				+ "<featureOrder userDefined=\"false\"/>\r"
				+ "</featureModel>\r");
		return sb;
	}

}
