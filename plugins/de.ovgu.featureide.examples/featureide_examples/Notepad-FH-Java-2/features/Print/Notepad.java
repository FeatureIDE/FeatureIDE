
class Notepad {
	protected JMenu buildFileMenu() {
		JMenu fileMenu   = original();
		if (fileMenu.getItemCount() > 0) fileMenu.addSeparator();
		JMenuItem printMenuItem  = new JMenuItem("Print", new ImageIcon(this.getClass().getResource("images/print.gif")));
		printMenuItem.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_P, ActionEvent.CTRL_MASK));
		printMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.print();
			}
		});
		fileMenu.add(printMenuItem);
		return fileMenu;
	}
	protected JToolBar buildToolBar() {
		JToolBar toolBar = original();
		if (toolBar.getComponentCount() > 0) toolBar.addSeparator();
		JButton printButton = new JButton(new ImageIcon(this.getClass().getResource("images/print.gif")));
		printButton.setToolTipText("Print");
		printButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.print();
			}
		});
		toolBar.add(printButton);
		return toolBar;
	}
}
