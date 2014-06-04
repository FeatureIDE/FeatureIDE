
class Actions {
	//declaration of the private variables used in the program
	private String findWord; //for searching & finding the word
	private int findIndex = -1;
	//this is a method for searching the input text from the text area
	public void find(){
		try{
			int index;
			findWord = JOptionPane.showInputDialog("Type the word to find");
			findIndex = n.getTextComponent().getText().indexOf(findWord);
			if (findIndex == -1) {
				JOptionPane.showMessageDialog(null,"Word not found!","No match",JOptionPane.WARNING_MESSAGE);
			} else {
				selectFound();
			}
		} catch (Exception ex) { }
	}
	public void findNext() {
		if (findIndex == -1) return;
		findIndex = n.getTextComponent().getText().indexOf(findWord, findIndex+1);
		if (findIndex == -1) {
			JOptionPane.showMessageDialog(null,"Search wrapped!","Search wrapped",JOptionPane.WARNING_MESSAGE);
			findIndex = n.getTextComponent().getText().indexOf(findWord);
		}
		if (findIndex != -1) selectFound();
	}
	private void selectFound() {
		n.getTextComponent().grabFocus();
		n.getTextComponent().select(findIndex, findIndex + findWord.length());
	}
}
