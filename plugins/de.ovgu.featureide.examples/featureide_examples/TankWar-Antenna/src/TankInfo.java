
import java.awt.Color;
import javax.swing.JFrame;
import javax.swing.JButton;

import javax.swing.Popup;
import javax.swing.PopupFactory;

public class TankInfo
{
   JFrame frame;
   Popup popup;

   public TankInfo()
   {
      frame = new JFrame("Tank - Info");
      frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
      frame.setBackground(Color.BLACK);
      frame.setSize(300, 300);

      PopupFactory factory = PopupFactory.getSharedInstance();
      popup = factory.getPopup(frame, new JButton("JButton"), 50, 50);
      popup.show();

      frame.setVisible(true);
   }

}
