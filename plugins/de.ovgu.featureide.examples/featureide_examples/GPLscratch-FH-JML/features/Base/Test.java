import java.util.Random;

/**
 * TODO description
 */
public class Test {
	static Random RANDOM = new Random();
	static final int MAX = 5;
	
	public static void main(String args[]) {
		Graph graph = new Graph();
		addNodes(graph);
		addEdgesFromExisitingNodes(graph);
		addEdgesNewNodes(graph);
		graph.print();
	}
	
	static void addNodes(Graph g){
		for (int i = 0; i < MAX; i++) {
			g.addNode(new Node("NODE-" + String.valueOf(i)));
		}
	}
}