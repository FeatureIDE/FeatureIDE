

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
  private JButton undo;
  private JButton redo;
  private void setUndoRedoAvailable(){
    redo.setEnabled(model.redoAvailable());
    undo.setEnabled(model.undoAvailable());
  }
  ButtonsToolBar(  ModelObservable mod,  final GenerationScheduler sched){
    undo=makeNavigationButton("Undo24","Rückgängig","Rückgängig","Undo",new ActionListener(){
      public void actionPerformed(ActionEvent e){
        if (model.undoAvailable()) {
          model.undo();
        }
      }
    }
	);
    undo.setEnabled(false);
    add(undo);
    redo=makeNavigationButton("Redo24","Wiederholen","Wiederholen","Redo",new ActionListener(){
      public void actionPerformed(ActionEvent e){
        if (model.redoAvailable()) {
          model.redo();
        }
      }
    }
	);
    redo.setEnabled(false);
    add(redo);
  }
  public void update(){
    setUndoRedoAvailable();
    original();
  }
}
