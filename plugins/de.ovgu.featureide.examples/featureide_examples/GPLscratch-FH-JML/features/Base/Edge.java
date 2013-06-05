/**
 * TODO description
 */
public class Edge {
	private Node source, dest;
	private double weight;

	public Edge(Node source, Node dest) {
		this(source, dest, Double.POSITIVE_INFINITY);
	}

	public Edge(Node source, Node dest, double weight) {
		this.source = source;
		this.dest = dest;
		this.weight = weight;
	}

//	@Override
	/*
	 * @ requires ob instanceof Edge && ob != null &&
	 * this.source.equals(((Edge)ob).getSource()) &&
	 * this.dest.equals(((Edge)ob).getDest())
	 * ensures this == ob
	 * also
	 * ensures this != ob
	 */
	public boolean equals(Object ob) {
		if (ob != null && (ob instanceof Edge)) {
			Edge e = (Edge) ob;
			if (this.source.equals(e.getSource())
					&& this.dest.equals(e.getDest()))
				return true;
		}
		return false;
	}

	@Override
	public String toString() {
		return source + " -" + weight + "-> " + dest;
	}

	public Node getSource() {
		return source;
	}

	public Node getDest() {
		return dest;
	}

	public double getWeight() {
		return weight;
	}
}