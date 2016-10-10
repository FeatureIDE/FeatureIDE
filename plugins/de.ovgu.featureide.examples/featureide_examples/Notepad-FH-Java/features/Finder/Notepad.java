import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;

class Notepad {

    private JButton findButton;
    private JMenuItem finD, findNexT;

     Notepad(){
        ediT.add(finD = new JMenuItem("Find", new ImageIcon(this.getClass().getResource("images/find.gif"))));
        ediT.add(findNexT = new JMenuItem("Find Next"));
        //ediT.insertSeparator(8);

        /**
         *allowing the finD      menu item to be selected by pressing ALT + F
         *allowing the findNexT  menu item to be selected by pressing ALT + F3
         */
        finD.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_F, ActionEvent.CTRL_MASK));
        findNexT.setAccelerator(KeyStroke.getKeyStroke(KeyEvent.VK_F3, ActionEvent.CTRL_MASK));
        toolBar.add(findButton  = new JButton(new ImageIcon(this.getClass().getResource("images/find.gif"))));
        findButton.setToolTipText("Find");

        finD.addActionListener(new ActionListener(){
            public void actionPerformed(ActionEvent ae){
                actions.finD();
            }
        });
        findNexT.addActionListener(new ActionListener(){
            public void actionPerformed(ActionEvent ae){
                actions.findNexT();
            }
        });

        findButton.addActionListener(new ActionListener(){
            public void actionPerformed(ActionEvent ae){
                actions.finD();
            }
        });
    }
}
