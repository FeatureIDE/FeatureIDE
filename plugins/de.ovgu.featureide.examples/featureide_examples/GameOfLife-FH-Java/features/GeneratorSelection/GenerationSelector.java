

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.List;

import javax.swing.JMenuItem;
import javax.swing.JPopupMenu;

import generator.GeneratorStrategy;

public class GenerationSelector extends JPopupMenu {

	public GenerationSelector(ModelObservable godlModel) {
		List gens = godlModel.getGeneratorStrategies();
		for (int i = 0; i < gens.size(); i++) {
			add(new GeneratorMenuItem((GeneratorStrategy) gens.get(i), godlModel));
		}
	}
	
	private class GeneratorMenuItem extends JMenuItem {
		GeneratorStrategy gen;
		private ModelObservable godlModel;
		public GeneratorMenuItem(final GeneratorStrategy gen, final ModelObservable godlmodel) {
			this.godlModel = godlmodel;
			this.gen = gen;
			this.setText(gen.toString());
			this.addActionListener(new ActionListener() {				
				public void actionPerformed(ActionEvent e) {
					GenerationSelector.this.setVisible(false);
					godlmodel.setGenerator(gen);
					godlmodel.generate();
				}
			});
		}
	}
}
