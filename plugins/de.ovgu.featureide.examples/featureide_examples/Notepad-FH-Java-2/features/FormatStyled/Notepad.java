
class Notepad {
	Notepad() {
		StyledDocument doc = getTextPane().getStyledDocument();
		Style regular = doc.addStyle("regular", 
			StyleContext.getDefaultStyleContext().getStyle(StyleContext.DEFAULT_STYLE));
		Style italic = doc.addStyle("italic", regular);
		StyleConstants.setItalic(italic, true);
		Style bold = doc.addStyle("bold", regular);
		StyleConstants.setBold(bold, true);
	}
	protected JToolBar buildToolBar() {
		JToolBar toolBar = original();
		if (toolBar.getComponentCount() > 0) toolBar.addSeparator();
		String styles[] = {"regular", "bold", "italic"};
		final JComboBox styleBox = new JComboBox(styles);
		styleBox.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent ae) {
				actions.setStyle(String.valueOf(styleBox.getSelectedItem()));
			}
		});
		toolBar.add(styleBox);
		return toolBar;
	}
}
