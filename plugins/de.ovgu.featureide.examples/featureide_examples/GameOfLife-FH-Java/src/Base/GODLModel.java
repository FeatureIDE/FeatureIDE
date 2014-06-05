

import java.util.Iterator; 
import java.util.ArrayList; 
import java.util.Collections; 
import java.util.List; 

public  class  GODLModel  extends ModelObservable {
	

	private RuleSet rules;

	
	private Playground playground;

	
	private List generators;

	
	
	public GODLModel(int xSize, int ySize, RuleSet rules) {
		this.rules = rules;
		this.playground = new Playground(xSize, ySize, 0);
		this.generators = new java.util.ArrayList();
	}

	
	
	
	public void setLifeform(int x, int y, int value) {
		playground.set(x, y, value);
		notifyObservers();
	}

	
		
	public void setPlayground(int[][] pg) {
		Playground newGround = new Playground(pg.length, pg[0].length, 0);
		for(int i = 0; i < pg.length; i++) {
			for(int j = 0; j < pg[i].length; j++) {
				newGround.set(i, j, pg[i][j]);
			}
		}
		this.playground = newGround;
		notifyObservers();
	}

	
	
	public void nextGeneration() {
		Playground newGround = new Playground(playground.getXSize(), playground.getYSize(), playground.getGeneration() + 1);
		Iterator it = playground.iterator();
		while(it.hasNext()) {
			LifeForm current = (LifeForm) it.next();
            newGround.set(current.getX(), current.getY(),  rules.apply(current));
		}
		this.playground = newGround;
		notifyObservers();
	}

	
			
	public int[][] getPlayground() {
		return playground.getField();
	}


}
