import java.util.Random;

/**
 * TODO description
 */
public class Test {
	static Random RANDOM = new Random();
	static final int MAX = 10;
	static final int MAXEDGES = 25;
	
//	public static void main(String args[]) {
//		Graph graph = new Graph();
//		addNodes(graph);
//		addEdgesFromExisitingNodes(graph);
//		addEdgesNewNodes(graph);
//		graph.print();
//		System.out.println();
//		graph.search(graph.getNodes().get(RANDOM.nextInt(MAX)));
//	}
//	
//	static void addNodes(Graph g){
//		for (int i = 0; i < MAX; i++) {
//			g.addNode(new Node("NODE-" + String.valueOf(i)));
//		}
//	}
//	
//	static void addEdgesFromExisitingNodes(Graph g) {
//		for (int j = 0; j < MAXEDGES; j++) {
//			g.addEdge(g.getNodes().get(RANDOM.nextInt(MAX)),
//					g.getNodes().get(RANDOM.nextInt(MAX)));
//		}
//	}
//
//	static void addEdgesNewNodes(Graph g) {
//		for (int j = 0; j < MAXEDGES; j++) {
//			g.addEdge(new Node("NODE-" + RANDOM.nextInt(MAX * 2)), new Node(
//					"NODE-" + RANDOM.nextInt(MAX * 2)));
//		}
//	}
}