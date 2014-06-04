

import java.util.Timer; 
import java.util.TimerTask; 

public  class  GenerationScheduler {
	
  private boolean active=false;

	
  private final static int timeRate=500;

	
  private Timer myTimer;

	
  private ModelObservable model;

	
  /** 
 * @param model
 */
  public GenerationScheduler(ModelObservable model){
    super();
    this.model=model;
  }

	
  public void start(){
    if (active) {
      return;
    }
    this.active=true;
    myTimer=new Timer();
    myTimer.scheduleAtFixedRate(new GenerationTask(),0,timeRate);
    System.out.println("started");
  }

	
  public void stop(){
    if (!active) {
      return;
    }
    this.active=false;
    if (myTimer == null) {
      throw new InternalError();
    }
    myTimer.cancel();
    myTimer=null;
    System.out.println("stopped");
  }

	
  public void singleStep(){
    model.nextGeneration();
  }

	
private  class  GenerationTask  extends TimerTask {
		
    public void run(){
      model.nextGeneration();
      model.notifyObservers();
    }


	}


}
