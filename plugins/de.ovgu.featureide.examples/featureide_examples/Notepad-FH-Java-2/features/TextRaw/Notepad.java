
import javax.swing.text.*;

class Notepad {
	//declaration of the private variables used in the program
	//create the text area
	private JTextArea textArea;
	Notepad() {
		Container cp = getContentPane();
		textArea = new JTextArea();
		textArea.setLineWrap(false);
		textArea.setWrapStyleWord(false);
		cp.add(textArea);
		cp.add(new JScrollPane(textArea));
	}
	public JTextArea getTextArea() {
		return textArea;
	}
	public JTextComponent getTextComponent() {
		return textArea;
	}
}
