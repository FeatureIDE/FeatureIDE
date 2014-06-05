
class Notepad {
	Notepad() {
		JToolBar toolBar = buildToolBar();
		if (toolBar.getComponentCount() > 0) {
			getContentPane().add("North", toolBar);
		}
	}
}
