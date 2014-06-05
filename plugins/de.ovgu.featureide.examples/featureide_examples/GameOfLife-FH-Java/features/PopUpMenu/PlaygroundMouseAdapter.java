

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import javax.swing.JPanel;
import javax.swing.JPopupMenu;

class PlaygroundMouseAdapter {
		
		public boolean hook(MouseEvent e, int x, int y) {
			if (e.isPopupTrigger() || e.getButton()==MouseEvent.BUTTON3) {
	            JPopupMenu popup = new PopUpMenu(playgroundPanel.getModel(), x, y);
	            popup.show(playgroundPanel,
	                       e.getX(), e.getY());
	            return true;
	        } else {
	        	return false;
	        }
		}
}