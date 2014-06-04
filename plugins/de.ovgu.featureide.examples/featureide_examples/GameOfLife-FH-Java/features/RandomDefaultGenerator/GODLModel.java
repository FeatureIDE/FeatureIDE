


class GODLModel {
	GODLModel(int xSize, int ySize, RuleSet rules) {
		for (int i = 0;  i < generators.size(); i++) {
			if (generators.get(i) instanceof RandomGeneratorStrategy) {
				generator = (GeneratorStrategy) generators.get(i);
				break;
			}
		}  
	}
}