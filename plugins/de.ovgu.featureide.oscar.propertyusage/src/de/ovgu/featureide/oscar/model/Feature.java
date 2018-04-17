package de.ovgu.featureide.oscar.model;

import java.util.HashSet;
import java.util.Set;

public class Feature {
	public String name;
	public boolean value;
	public FeatureType type;
	public boolean isAbstract=false;
	public Set<Feature> hierarchy= new HashSet<Feature>();
	
	public Feature(String name, boolean value, FeatureType type) {
		super();
		this.name = name;
		this.value = value;
		this.type = type;

	}
	public void addHierarchy(Feature feat){
		hierarchy.add(feat);
	}
	
	public void addHierarchy(Set<Feature> feats){
		hierarchy.addAll(feats);
	}

	public boolean isAbstract() {
		return isAbstract;
	}
	public void setAbstract(boolean isAbstract) {
		this.isAbstract = isAbstract;
	}
	@Override
	public boolean equals(Object obj) {
		if (obj == null) {
	        return false;
	    }
		if (!Feature.class.isAssignableFrom(obj.getClass())) {
	        return false;
	    }
	    final Feature other = (Feature) obj;
		
		return this.name.equals(other.name) && (this.type==other.type)&&(this.hierarchy.equals(other.hierarchy));
	}
	@Override
	public String toString() {
		
		StringBuilder sb = new StringBuilder ();
		switch (this.type){
		
			case ALL:
				break;
			case ATOMIC:
				sb.append("<feature name=\""+this.name+"\"/>");
				break;
			case MORE_OF:
				break;
			case ONE_OF:
				break;
			default:
				break;
			
		
		}
		
		return sb.toString();
	}
	
	public Feature getFeature(String name){
		if (this.name.equals(name)) return this;
		Feature res=null;
		for (Feature f:hierarchy){
			if (f.name.equals(name)) return f;
			res=f.getFeature(name);
			if ( res !=null) return res; 
		}
		return null;
		
	}

}
