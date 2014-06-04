
class Notepad {
	protected JMenu buildEditMenu() {
		JMenu editMenu = original();
		if (editMenu.getItemCount() > 0) editMenu.addSeparator();
		JMenuItem cutMenuItem  = new JMenuItem("Cut",  new ImageIcon(this.getClass().getResource("images/cut.gif")));
		cutMenuItem.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_X, ActionEvent.CTRL_MASK));
		cutMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.cut();
			}
		});
		editMenu.add(cutMenuItem);
		JMenuItem copyMenuItem = new JMenuItem("Copy", new ImageIcon(this.getClass().getResource("images/copy.gif")));
		copyMenuItem.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_C, ActionEvent.CTRL_MASK));
		copyMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.copy();
			}
		});
		editMenu.add(copyMenuItem);
		JMenuItem pasteMenuItem= new JMenuItem("Paste",new ImageIcon(this.getClass().getResource("images/paste.gif")));
		pasteMenuItem.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_V, ActionEvent.CTRL_MASK));
		pasteMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.paste();
			}
		});
		editMenu.add(pasteMenuItem);
		JMenuItem selectAllMenuItem= new JMenuItem("Select All");
		selectAllMenuItem.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_A, ActionEvent.CTRL_MASK));
		selectAllMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.selectAll();
			}
		});
		editMenu.add(selectAllMenuItem);
		return editMenu;
	}
	protected JToolBar buildToolBar() {
		JToolBar toolBar = original();
		if (toolBar.getComponentCount() > 0) toolBar.addSeparator();
		JButton cutButton   = new JButton(new ImageIcon(this.getClass().getResource("images/cut.gif")));
		cutButton.setToolTipText("Cut");
		cutButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.cut();
			}
		});
		toolBar.add(cutButton);
		JButton copyButton  = new JButton(new ImageIcon(this.getClass().getResource("images/copy.gif")));
		copyButton.setToolTipText("Copy");
		copyButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.copy();
			}
		});
		toolBar.add(copyButton);
		JButton pasteButton = new JButton(new ImageIcon(this.getClass().getResource("images/paste.gif")));
		pasteButton.setToolTipText("Paste");
		pasteButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.paste();
			}
		});
		toolBar.add(pasteButton);
		return toolBar;
	}
}
