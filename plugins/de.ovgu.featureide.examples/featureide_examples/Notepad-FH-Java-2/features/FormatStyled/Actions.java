
class Actions {
	//for wraping the line & wraping the style word
	public void setStyle(String style) {
		n.getTextPane().setCharacterAttributes(
			n.getTextPane().getStyledDocument().getStyle(style), true);
	}
}
