
class Notepad {
	protected JMenu buildFileMenu() {
		JMenu fileMenu   = original();
		if (fileMenu.getItemCount() > 0) fileMenu.addSeparator();
		JMenuItem newFileMenuItem    = new JMenuItem("New", new ImageIcon(this.getClass().getResource("images/new.gif")));
		newFileMenuItem.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_N, ActionEvent.CTRL_MASK));
		newFileMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.newFile();
			}
		});
		fileMenu.add(newFileMenuItem);
		JMenuItem openMenuItem   = new JMenuItem("Open", new ImageIcon(this.getClass().getResource("images/open.gif")));
		openMenuItem.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_O, ActionEvent.CTRL_MASK));
		openMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.open();
			}
		});
		fileMenu.add(openMenuItem);
		JMenuItem saveMenuItem   = new JMenuItem("Save", new ImageIcon(this.getClass().getResource("images/save.gif")));
		saveMenuItem.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_S, ActionEvent.CTRL_MASK));
		saveMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.save();
			}
		});
		fileMenu.add(saveMenuItem);
		JMenuItem saveAsMenuItem = new JMenuItem("Save As", new ImageIcon(this.getClass().getResource("images/saveAs.gif")));
		saveAsMenuItem.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.saveAs();
			}
		});
		fileMenu.add(saveAsMenuItem);
		return fileMenu;
	}
	protected JToolBar buildToolBar() {
		JToolBar toolBar = original();
		if (toolBar.getComponentCount() > 0) toolBar.addSeparator();
		JButton newButton   = new JButton(new ImageIcon(this.getClass().getResource("images/new.gif")));
		newButton.setToolTipText("New");
		newButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.newFile();
			}
		});
		toolBar.add(newButton);
		JButton openButton  = new JButton(new ImageIcon(this.getClass().getResource("images/open.gif")));
		openButton.setToolTipText("Open");
		openButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.open();
			}
		});
		toolBar.add(openButton);
		JButton saveButton  = new JButton(new ImageIcon(this.getClass().getResource("images/save.gif")));
		saveButton.setToolTipText("Save");
		saveButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.save();
			}
		});
		toolBar.add(saveButton);
		JButton saveAsButton= new JButton(new ImageIcon(this.getClass().getResource("images/saveAs.gif")));
		saveAsButton.setToolTipText("Save As");
		saveAsButton.addActionListener(new ActionListener(){
			public void actionPerformed(ActionEvent ae){
				actions.saveAs();
			}
		});
		toolBar.add(saveAsButton);
		return toolBar;
	}
}
