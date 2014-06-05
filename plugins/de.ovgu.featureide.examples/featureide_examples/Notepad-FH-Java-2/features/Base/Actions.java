
//import the packages for using the classes in them into this class
import java.io.*;
import java.util.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.filechooser.*;

/**
 *A PUBLIC CLASS FOR ACTIONS.JAVA
 */
public class Actions {
	Notepad n; //for using the object in the Notepad.java

	public Actions(Notepad n){
		this.n = n;
	}
	public void exit(){
		System.exit(0);
	}
	/**
	 *@see ABOUT.JAVA
	 *it's a Message Dialog to show the information about this program
	 */
	public void about(){
		JOptionPane.showMessageDialog(null, new About(),"About Notepad",JOptionPane.PLAIN_MESSAGE);
	}
}
