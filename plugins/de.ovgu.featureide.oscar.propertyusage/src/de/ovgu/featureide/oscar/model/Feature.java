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
	
	public FeatureType getType() {
		return type;
	}
	public void setType(FeatureType type) {
		this.type = type;
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
		
		return this.name.equals(other.name);
	}
	@Override
	public String toString() {
		
		StringBuilder sb = new StringBuilder ();
		switch (this.type){
		
			case ALL:
				sb.append("	<and name=\""+this.name+"\""+(this.isAbstract?" abstract=\"true\"":"")+">\r");
				for(Feature f:this.hierarchy){
					sb.append(f.toString());
				}
				sb.append("	</and>\r");
				break;
			case ATOMIC:
				sb.append("	<feature name=\""+this.name+(this.isAbstract?" abstract=\"true\"":"")+"\"/>\r");
				break;
			case MORE_OF:
				sb.append("	<alt name=\""+this.name+"\""+(this.isAbstract?" abstract=\"true\"":"")+">\r");
				for(Feature f:this.hierarchy){
					sb.append(f.toString());
				}
				sb.append("	</alt>\r");
				break;
			case ONE_OF:
				sb.append("	<or name=\""+this.name+"\""+(this.isAbstract?" abstract=\"true\"":"")+">\r");
				for(Feature f:this.hierarchy){
					sb.append(f.toString());
				}
				sb.append("	</or>\r");
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
			if (f.name.toLowerCase().equals(name.toLowerCase())) return f;
			res=f.getFeature(name);
			if ( res !=null) return res; 
		}
		return null;
		
	}

}
