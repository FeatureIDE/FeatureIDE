

import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.File;
import java.io.IOException;
import java.net.URL;
import javax.swing.AbstractAction;
import javax.swing.Action;
import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JPanel;
import javax.swing.JToolBar;

class ButtonsToolBar {
  ButtonsToolBar(ModelObservable mod,  final GenerationScheduler sched){
    add(makeNavigationButton("open24","Load","Laden","Laden",new ActionListener(){
      public void actionPerformed(ActionEvent e){
        JFileChooser fc=new JFileChooser();
        int resp=fc.showOpenDialog(ButtonsToolBar.this);
        if (resp == JFileChooser.APPROVE_OPTION) {
          	File selected=fc.getSelectedFile();
          	if (selected == null || !selected.exists())           
          		return;
          	try {
            	model.setPlayground(PlaygroundIO.loadFromFile(selected));
          	} catch (          IOException e1) {
            	e1.printStackTrace();
          	}
        }
      }
    }
	));
    add(makeNavigationButton("Save24","Save","Speichern","Speichern",new ActionListener(){
      public void actionPerformed(ActionEvent e){
        JFileChooser fc=new JFileChooser();
        int resp=fc.showSaveDialog(ButtonsToolBar.this);
        if (resp == JFileChooser.APPROVE_OPTION) {
          	File selected=fc.getSelectedFile();
          	if (selected == null)
          		return;
          	try {
            	PlaygroundIO.saveToFile(model.getPlayground(),selected);
          	} catch (IOException e1) {
            	e1.printStackTrace();
          	}
        }
      }
    }
	));
  }
}
