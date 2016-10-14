import java.util.ArrayList;
import java.util.Random;

/**
 * TODO description
 */
public class Test {
	static Random RANDOM = new Random();
	Graph graph = new Graph();
	
	public void run() {
		original();
		
		Node source = (Node) graph.getNodes().toArray()[RANDOM.nextInt(graph.getNodes().size())];
		Node target = (Node) graph.getNodes().toArray()[RANDOM.nextInt(graph.getNodes().size())];
		// Is there Path between source and target?
		System.out.println("Gibt es eine Verbindung von " + source + " nach " + target + "?");
		System.out.println("\t"+graph.hasConnection(source, target));
		
		// If yes, get this Path
		if (graph.hasConnection(source, target)) {
			System.out.println("Folgender Pfad verbindet " + source + " und " + target);
			ArrayList<Node> path = graph.getConnection(source, target);
			System.out.println("\t" + path);
			
			System.out.println("Ist der Pfad wirklich korrekt?");
			System.out.println("\t" + graph.isConnection(path, source, target));
		}
		
	}
	
}