package de.ovgu.featureide.fm.core.constraint;

public class WeightedTerm {

	private int weight;
	
	private boolean positive;
	
	private Reference reference;

	public WeightedTerm(int weight, boolean positive, Reference reference) {
		this.weight = weight;
		this.positive = positive;
		this.reference = reference;
	}

	public int getWeight() {
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
