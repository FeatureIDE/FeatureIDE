
import javax.swing.text.*;

class Notepad {
	//declaration of the private variables used in the program
	//create the text area
	private JTextPane textPane;
	Notepad() {
		Container cp = getContentPane();
		textPane = new JTextPane();
		cp.add(textPane);
		cp.add(new JScrollPane(textPane));
	}
	public JTextPane getTextPane() {
		return textPane;
	}
	public JTextComponent getTextComponent() {
		return textPane;
	}
}
