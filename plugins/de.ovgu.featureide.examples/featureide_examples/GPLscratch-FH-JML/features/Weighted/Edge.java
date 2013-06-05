/**
 * TODO description
 */
public class Edge {
	private int weight;

	public Edge(Node n1, Node n2, int weight) {
		this.n1 = n1;
		this.n2 = n2;
		this.weight = weight;
	}
	
	public int getWeight(){
		return weight;
	}
}