
class Notepad {
	protected JMenu buildEditMenu() {
		JMenu editMenu   = original();
		if (editMenu.getItemCount() > 0) editMenu.addSeparator();
		JMenuItem findMenuItem = new JMenuItem("Find", new ImageIcon(this.getClass().getResource("images/find.gif")));
		findMenuItem.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_F, ActionEvent.CTRL_MASK));
		findMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.find();
			}
		});
		editMenu.add(findMenuItem);
		JMenuItem findNextMenuItem = new JMenuItem("Find Next");
		findNextMenuItem.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_G, ActionEvent.CTRL_MASK));
		findNextMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.findNext();
			}
		});
		editMenu.add(findNextMenuItem);
		return editMenu;
	}
	protected JToolBar buildToolBar() {
		JToolBar toolBar = original();
		if (toolBar.getComponentCount() > 0) toolBar.addSeparator();
		JButton findButton  = new JButton(new ImageIcon(this.getClass().getResource("images/find.gif")));
		findButton.setToolTipText("Find");
		findButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.find();
			}
		});
		toolBar.add(findButton);
		return toolBar;
	}
}
