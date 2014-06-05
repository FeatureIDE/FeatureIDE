
class Notepad {
	private JCheckBoxMenuItem lineWrapMenuItem;
	//for using lineWrap & textArea @Actions.java
	public JCheckBoxMenuItem getLineWrap(){
		return lineWrapMenuItem;
	}
	protected JMenu buildFormatMenu() {
		JMenu formatMenu = original();
		if (formatMenu.getItemCount() > 0) formatMenu.addSeparator();
		lineWrapMenuItem = new JCheckBoxMenuItem("Line Wrap");
		lineWrapMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.lineWrap();
			}
		});
		formatMenu.add(lineWrapMenuItem);
		JMenuItem fontMenuItem = new JMenuItem("Font", new ImageIcon(this.getClass().getResource("images/font.gif")));
		fontMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.font();
			}
		});
		formatMenu.add(fontMenuItem);
		return formatMenu;
	}
	protected JToolBar buildToolBar() {
		JToolBar toolBar = original();
		if (toolBar.getComponentCount() > 0) toolBar.addSeparator();
		JButton fontButton  = new JButton(new ImageIcon(this.getClass().getResource("images/font.gif")));
		fontButton.setToolTipText("Font");
		fontButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.font();
			}
		});
		toolBar.add(fontButton);
		return toolBar;
	}
}
