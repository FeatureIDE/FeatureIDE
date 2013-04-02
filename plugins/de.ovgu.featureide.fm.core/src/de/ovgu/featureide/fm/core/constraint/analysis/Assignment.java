package de.ovgu.featureide.fm.core.constraint.analysis;

/**
 * This class represents a boolean variable assignment which can be either true,
 * false, or unassigned (null). It is identified by an integer ID.
 * 
 * @author Sebastian Henneberg
 */
public class Assignment implements Cloneable {

	private int id;
	private boolean assignment;
	
	public Assignment(int id, boolean assignment) {
		this.id = id;
		this.assignment = assignment;
	}

	public int getId() {
		return id;
	}

	public boolean getAssignment() {
		return assignment;
	}
	
	@Override
	public String toString() {
		return String.format("%s=%s", id, assignment);
	}
	
	@Override
	protected Object clone() throws CloneNotSupportedException {
		Assignment object = (Assignment) super.clone();
		object.id = id;
		object.assignment = assignment;
		return object;
	}
}
