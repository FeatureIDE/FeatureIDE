package de.ovgu.featureide.fm.extended.ui.io.constraint;

public class Reference {

	private String featureName;
	
	private ReferenceType type;
	
	private String attributeName = null;

	public Reference(String featureName, ReferenceType type, String attributeName) {
		this.featureName = featureName;
		this.type = type;
		this.attributeName = attributeName;
	}
	
	public Reference(String featureName) {
		this.featureName = featureName;
		this.type = ReferenceType.FEATURE;
	}

	public String getFeatureName() {
		return featureName;
	}

	public ReferenceType getType() {
		return type;
	}

	public String getAttributeName() {
		return attributeName;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(featureName);
		
		switch (type) {
		case ATTRIBUTE:
			sb.append(".");
			sb.append(attributeName);
			break;
		case ATTRIBUTE_SUM:
			sb.append("#.");
			sb.append(attributeName);
			break;
		}
		
		return sb.toString();
	}
}
