import java.util.List;

import interfaces.Announce;
import interfaces.Print;
import loader.PluginLoader;

public class Main {
	public static void main(String[] args) throws InterruptedException {
		List<Print> printingClasses = PluginLoader.load(Print.class);
		List<Announce> announcingClasses = PluginLoader.load(Announce.class);
		
		for(Print p : printingClasses){
			p.print();
		}
		Thread.sleep(100);
		for(Announce a : announcingClasses){
			a.announce();
		}
	}
}
