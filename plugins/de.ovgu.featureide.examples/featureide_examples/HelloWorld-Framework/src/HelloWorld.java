import java.util.List;

import interfaces.IMessage;
import loader.PluginLoader;

public class HelloWorld {
	
	public static void main(String[] args) throws InterruptedException {
		List<IMessage> messagePlugins = PluginLoader.load(IMessage.class);
		print(messagePlugins, true);
		print(messagePlugins, false);
	}

	private static void print(List<IMessage> messagePlugins, boolean startMessage) {
		for (IMessage message : messagePlugins) {
			if (message.isStartMessage() == startMessage) {
				System.out.print(message.getMessage());
			}
		}
	}
	
}
