


import generator.FormGeneratorStrategy;

class GODLModel {
	
	GODLModel(int xSize, int ySize, RuleSet rules) {
		FormGeneratorStrategy fgs = new FormGeneratorStrategy(playground.getXSize(), playground.getYSize());
		generators.add(fgs);
	}

}