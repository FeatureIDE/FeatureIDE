

import java.awt.BorderLayout; 
import javax.swing.BoxLayout; 
import javax.swing.JFrame; 

public  class  GolView  extends JFrame  implements ModelObserver {
	
  private ModelObservable model;

	
  private PlaygroundPanel PPanel;

	
  private ButtonsToolBar BTBar;

	
  public GolView(  ModelObservable model){
    this.model=model;
    this.setDefaultCloseOperation(EXIT_ON_CLOSE);
    this.setLayout(new BorderLayout());
    final GenerationScheduler sched=new GenerationScheduler(model);
    PPanel=new PlaygroundPanel(model,sched);
    this.add(PPanel);
    BTBar=new ButtonsToolBar(model,sched);
    this.add(BTBar,BorderLayout.NORTH);
    this.pack();
    model.attach(this);
  }

	
  public void update(){
    PPanel.display(model.getPlayground());
    BTBar.update();
  }


}
