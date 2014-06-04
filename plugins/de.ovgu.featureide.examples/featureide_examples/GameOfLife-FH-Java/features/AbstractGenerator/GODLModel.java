


import generator.GeneratorStrategy;
import generator.ClearGeneratorStrategy;

class GODLModel {
	
	private GeneratorStrategy generator = null;
	GODLModel(int xSize, int ySize, RuleSet rules) {
		generators.add(new ClearGeneratorStrategy());
	}
	public void setGenerator(GeneratorStrategy generator) {
		this.generator = generator;
	}
	public List getGeneratorStrategies() {
		return java.util.Collections.unmodifiableList(this.generators);
	}
	
	public void generate() {
		if (generator == null) {
			generator = new ClearGeneratorStrategy();
		}
		Playground newGround = new Playground(playground.getXSize(), playground.getYSize(), 0);
		Iterator it = playground.iterator();
		while(it.hasNext()) {
			LifeForm current = (LifeForm) it.next();
			newGround.set(current.getX(), current.getY(), generator.getNext(current.getX(), current.getY()));
		}
		this.playground = newGround;
		notifyObservers();
	}
	
}