import javax.swing.undo.*;
import javax.swing.event.*;

class Notepad {
    //for using undo & redo
    UndoManager undo = new UndoManager();
    UndoAction undoAction = new UndoAction(this);
    RedoAction redoAction = new RedoAction(this);

    private JButton undoButton, redoButton;

     Notepad() {
	    ediT.add(undoAction);
	    ediT.add(redoAction);

	    toolBar.addSeparator();
	    toolBar.add(undoAction);
	    toolBar.add(redoAction);
	    toolBar.addSeparator();

	    textArea.getDocument().addUndoableEditListener(new UndoableEditListener(){
			    public void undoableEditHappened(UndoableEditEvent e){
			    //Remember the edit and update the menus
			    undo.addEdit(e.getEdit());
			    undoAction.update();
			    redoAction.update();
			    }
			    });
    }
}


