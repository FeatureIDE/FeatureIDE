

import java.util.List;
import generator.GeneratorStrategy;
import java.awt.Point;

class ButtonsToolBar {
  
    void addGenerationButton() {
/*		JMenu btn = new GenerationSelector(model);
		String imgLocation = "/ressources/images/" + "Stop24" + ".gif";
		URL imageURL = Main.class.getResource(imgLocation);
		btn.setActionCommand("Generate");
		btn.setToolTipText("neues Feld generieren");
		if (imageURL != null) {
			btn.setIcon(new ImageIcon(imageURL, "Generieren"));
		} else {
			btn.setText("Generieren");
			System.err.println("Resource not found: " + imgLocation);
		}
		
		add(btn);*/
    	
  	  final JButton btn = makeNavigationButton("Stop24","ClearField","Feld generieren","generieren",new ActionListener(){
	      public void actionPerformed(ActionEvent e){
	    	  List gens = model.getGeneratorStrategies();
	    	  if (gens.size() == 1) {
	    		  model.setGenerator((GeneratorStrategy) gens.get(0));
	    		  model.generate();
	    		  return;
	    	  } else if (gens.size() == 0) {
	    		  model.generate();
	    		  return;
	    	  }
	    	  sched.stop();
        	  pause.setEnabled(false);
        	  play.setEnabled(true);
	    	  GenerationSelector s = new GenerationSelector(model);
	    	  Point p = ((JButton)e.getSource()).getLocationOnScreen();
	    	  p.y = p.y + ((JButton)e.getSource()).getHeight();
	    	  s.setLocation(p);
	    	  //s.setLocation(((JButton)e.getSource()).getX(), ((JButton)e.getSource()).getY() + ((JButton)e.getSource()).getHeight());
	    	  s.setVisible(true);
	      }
	  }
	  );
	  add(btn);
	}
}
