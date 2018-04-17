package de.ovgu.featureide.oscar.IO;

import java.io.IOException;

import org.eclipse.ui.console.ConsolePlugin;
import org.eclipse.ui.console.IConsole;
import org.eclipse.ui.console.IConsoleManager;
import org.eclipse.ui.console.MessageConsole;
import org.eclipse.ui.console.MessageConsoleStream;

public class Console {

	private final String CONSOLE_NAME="FeatureIDE";
	private MessageConsole mc; 

	public Console() {
		mc = findConsole(CONSOLE_NAME);
	}

	private MessageConsole findConsole(String name) {
	      ConsolePlugin plugin = ConsolePlugin.getDefault();
	      IConsoleManager conMan = plugin.getConsoleManager();
	      IConsole[] existing = conMan.getConsoles();
	      for (int i = 0; i < existing.length; i++)
	         if (name.equals(existing[i].getName()))
	            return (MessageConsole) existing[i];
	      //no console found, so create a new one
	      MessageConsole myConsole = new MessageConsole(name, null);
	      conMan.addConsoles(new IConsole[]{myConsole});
	      return myConsole;
   }
   
   public void writeln (String output){
	  MessageConsoleStream out=null;
	  try {
		  out = mc.newMessageStream();
		  out.setActivateOnWrite(true);
		  out.println(output);
		} finally {
			try {
				out.flush();
				out.close();
			} catch (IOException e) {
				
			}
		}
	   
   }
   
   public void write (String output){
		  MessageConsoleStream out=null;
		  try {
			  out = mc.newMessageStream();
			  out.setActivateOnWrite(true);
			  out.print(output);
			} finally {
				try {
					out.flush();
					out.close();
				} catch (IOException e) {
					
				}
			}
		   
	   }

}
