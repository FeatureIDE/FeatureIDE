import java.util.Random;

/**
 * TODO description
 */
public class Test {
	static Random RANDOM = new Random();
	static final int MAX = 10;
	static final int MAXEDGES = 25;
	
	Graph graph = new Graph();
	
	public static void main(String args[]) {
		Test test = new Test();
		test.run();
	}
	
	
	public void run() {
		initGraph();
		graph.print();
	}
	
	void initGraph() {
		addNodes();
		addEdges();
	}
	
	
//	
	void addNodes(){
		for (int i = 0; i < MAX; i++) {
			graph.addNode(new Node("node-" + String.valueOf(i)));
		}
	}
//	
	void addEdges() {
		for (int j = 0; j < MAXEDGES; j++) {
			graph.addEdge(new Edge((Node)graph.getNodes().toArray()[RANDOM.nextInt(MAX)],
					(Node)graph.getNodes().toArray()[RANDOM.nextInt(MAX)]));
		}
	}
}