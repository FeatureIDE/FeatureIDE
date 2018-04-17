package de.ovgu.featureide.oscar.propertyusage.core;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

import de.ovgu.featureide.oscar.IO.Console;
import de.ovgu.featureide.oscar.model.Feature;
import de.ovgu.featureide.oscar.model.FeatureType;
import oscar.OscarProperties;

public class HierarchyReconstruction {
	
	
	
	private static final Set<String> activeMarkers = new HashSet<String>(
			Arrays.asList(new String[] { "true", "yes", "on", "false", "no", "off" }));
	private static final String regx_split_list="[\\,\\|]";
	private static final Pattern regx_sep_list=Pattern.compile("\\w+"+regx_split_list+"\\w+");
	private static final String regx_split_key="[\\_\\-\\.]";
	//private static final String regx_split_key="[\\-\\.]";
	private static final Pattern regx_sep_key = Pattern.compile("\\w+"+regx_split_key+"\\w+");
	
	public static Feature getFDLHierarchy(OscarProperties op, Map<String, Integer[]> allPropMap, double threshold){
		
		//Create the Console to log the results
		final Console console = new Console();
		Feature base= new Feature("Base", true, FeatureType.ALL);
		base.setAbstract(true);
		
		for (String key:allPropMap.keySet()){
			try {
				int numerator=allPropMap.get(key)[1];
				int denominator=allPropMap.get(key)[0];
				double coef= (denominator > 0) ? ((1.0*numerator)/denominator) : 0.0;
				if (coef<threshold) continue;
				String value=op.getProperty(key);
				Feature current;
				if ((value == null) || (value.equals(""))){
					current=new Feature(key,false,FeatureType.ATOMIC);
				}else if (isBooleanProperty(value)){
					current=new Feature(key,Boolean.parseBoolean(value),FeatureType.ATOMIC);
				}else if (regx_sep_list.matcher(value).lookingAt()){ //the value is a list.
					current= new Feature(key, true, FeatureType.MORE_OF);
					current.setAbstract(true);
					for (String s: value.split(regx_split_list)){
						current.addHierarchy(new Feature(key+"."+s,true,FeatureType.ATOMIC));
					}					
				}else {
					current= new Feature(key, true, FeatureType.MORE_OF);
					current.setAbstract(true);
					current.addHierarchy(new Feature(key+"."+value,true,FeatureType.ATOMIC));
					//TO-DO: maybe mark this in red as to grab attention.
				}
				
				Feature father=base;
				if (regx_sep_key.matcher(key).lookingAt()){ //creating the fathers to current if it has fathers.
					String[] path=key.split(regx_split_key);
					Feature aux=null;
					for(int i=0; i < path.length - 1; i++){
						String name=key.substring(0,key.lastIndexOf(path[i])+path[i].length());
						aux=base.getFeature(name);
						if (aux==null){
							aux=new Feature(name,true,FeatureType.ALL);
							aux.setAbstract(true);
							father.addHierarchy(aux);
							father=aux;
						}else{
							aux.setType(FeatureType.ALL);
							father=aux;
						}
						
					}
				}
				father.addHierarchy(current);
			} catch (Exception e) {
				console.writeln("The property "+key+" could not be processed, error: "+ e.getMessage());
			}
			
		}
		return base;
		
	}
	
	private static boolean isBooleanProperty(String val) {
		val = val==null ? null : val.trim();
		// if we're checking for positive value, any "active" one will do
		return (val != null && activeMarkers.contains(val.toLowerCase()));
	}
		
	

}
