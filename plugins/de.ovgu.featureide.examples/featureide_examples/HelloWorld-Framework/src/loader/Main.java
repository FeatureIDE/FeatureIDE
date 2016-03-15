package loader;

import java.util.List;

import interfaces.Announce;
import interfaces.Print;

public class Main {
	public static void main(String[] args) {
		List<Print> printingClasses = PluginLoader.load(Print.class);
		List<Announce> announcingClasses = PluginLoader.load(Announce.class);
		
		for(Print p : printingClasses){
			p.print();
		}
		System.out.println();
		for(Announce a : announcingClasses){
			a.announce();
		}
	}
}
