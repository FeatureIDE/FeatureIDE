import java.util.Random;

/**
 * TODO description
 */
public class Test {
	static Random RANDOM = new Random();
	Graph graph = new Graph();
	
	void initGraph() {
		original();
		addWeights();
	}
	
	void addWeights() {
		for(Edge e : graph.getEdges()) 
			e.setWeight(RANDOM.nextInt(100));
	}
}