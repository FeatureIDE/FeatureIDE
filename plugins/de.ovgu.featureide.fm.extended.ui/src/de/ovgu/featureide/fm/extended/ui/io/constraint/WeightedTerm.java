package de.ovgu.featureide.fm.extended.ui.io.constraint;

public class WeightedTerm {

	private Integer weight;
	
	private boolean positive;
	
	private Reference reference;

	public WeightedTerm(Integer weight, boolean positive, Reference reference) {
		this.weight = weight;
		this.positive = positive;
		this.reference = reference;
	}

	public Integer getWeight() {
		return weight;
	}

	public boolean isPositive() {
		return positive;
	}

	public Reference getReference() {
		return reference;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(weight);
		sb.append(" ");
		if (!positive) 
			sb.append("~");
		sb.append(reference.toString());
		sb.append(")");
		return sb.toString();
	}
}
