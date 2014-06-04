

import javax.swing.SwingUtilities; 
import java.util.Arrays; 

public  class  Main {
	
  public static void main(  String[] args){
    SwingUtilities.invokeLater(new Runnable(){
      public void run(){
						boolean[] causesBirth = new boolean[9];
				boolean[] causesDeath = new boolean[9];
				Arrays.fill(causesDeath, true);
				causesDeath[2] = false;
				causesDeath[3] = false;
				causesBirth[3] = true;
        new GolView(new GODLModel(30,30,new RuleSet(causesBirth, causesDeath))).setVisible(true);
      }
    }
);
  }


}
