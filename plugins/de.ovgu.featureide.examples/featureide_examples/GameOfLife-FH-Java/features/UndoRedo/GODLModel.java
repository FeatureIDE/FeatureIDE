

import java.util.LinkedList;
import java.util.List;

class GODLModel {
	private final LinkedList undoList;
	private final LinkedList redoList;

    GODLModel(int xSize, int ySize, RuleSet rules) {
    	this.undoList = new LinkedList();
        this.redoList = new LinkedList();
    }
	
    public void setLifeform(int x, int y, int value) {
        undoList.push((Object) playground.clone());
        original(x, y, value);
	}

	public void setPlayground(int[][] pg) {
	    undoList.push((Object) playground.clone());
        original(pg);
	}

    public void nextGeneration() {
        undoList.push((Object) playground.clone());
        original();
    }

    public void undo() {
        redoList.push((Object) playground);
        playground = (Playground) undoList.pop();
        notifyObservers();
    }

    public void redo() {
        undoList.push((Object) playground);
        playground = (Playground) redoList.pop();
        notifyObservers();
    }
    
    public boolean undoAvailable() {
		return undoList != null && !undoList.isEmpty();
	}
	
	public boolean redoAvailable() {
		return redoList != null && !redoList.isEmpty();
	}
}