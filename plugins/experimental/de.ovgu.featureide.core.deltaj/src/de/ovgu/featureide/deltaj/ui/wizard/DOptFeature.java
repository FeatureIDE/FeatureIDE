package de.ovgu.featureide.deltaj.ui.wizard;

import java.util.ArrayList;

public class DOptFeature {
	
	private ArrayList<String> features;
	private String deltaModule;
	
	public DOptFeature(String deltamod, ArrayList<String> features){
		this.features=features;
		this.deltaModule = deltamod;
	}
	
	public ArrayList<String> getFeatures() {
		return features;
	}
	public void setFeature(ArrayList<String> feature) {
		this.features = feature;
	}
	public String getDeltaModule() {
		return deltaModule;
	}
	public void setDeltaModule(String deltaModule) {
		this.deltaModule = deltaModule;
	}
	
	public String getProp(){
		String prop ="";
		if(this.features.isEmpty())
			return null;
		else{
			
			for (String f : this.features) {
				if(!(f.equals(features.get(features.size()-1))))
					prop +=f+" && ";
				else
					prop +=f;
			}
			return prop;
		}
	}

}
