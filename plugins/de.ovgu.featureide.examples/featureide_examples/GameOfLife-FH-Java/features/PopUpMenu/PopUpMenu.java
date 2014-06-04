

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JPopupMenu;

public class PopUpMenu extends JPopupMenu {
  private ModelObservable model;
  int xCoordinate;
  int yCoordinate;
  public PopUpMenu(  ModelObservable model,  int x,  int y){
    this.xCoordinate=x;
    this.yCoordinate=y;
    this.model=model;
    this.add(new StaticObjectsMenu("statische Objekte"));
    this.add(new PulsatingObjectsMenu("pulsierende Objekte"));
    this.add(new MovingObjectsMenu("Raumschiffe/ Gleiter"));
  }
class StaticObjectsMenu extends JMenu {
    public StaticObjectsMenu(    String name){
      super(name);
      this.add(new static1());
      this.add(new static2());
      this.add(new static3());
      this.add(new static4());
    }
class static1 extends JMenuItem {
      ActionListener act=new ActionListener(){
        public void actionPerformed(        ActionEvent e){
          if (xCoordinate < 0 || xCoordinate > PopUpMenu.this.model.getPlayground().length - 3) {
            System.err.println("not in range");
            return;
          }
          if (yCoordinate < 0 || yCoordinate > PopUpMenu.this.model.getPlayground()[0].length - 3) {
            System.err.println("not in range");
            return;
          }
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 2,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 2,0);
        }
      }
;
      public static1(){
        super("static1");
        this.addActionListener(act);
      }
    }
class static2 extends JMenuItem {
      ActionListener act=new ActionListener(){
        public void actionPerformed(        ActionEvent e){
          if (xCoordinate < 0 || xCoordinate >= PopUpMenu.this.model.getPlayground().length - 3) {
            System.err.println("not in range");
            return;
          }
          if (yCoordinate < 0 || yCoordinate >= PopUpMenu.this.model.getPlayground()[0].length - 4) {
            System.err.println("not in range");
            return;
          }
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 2,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 2,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 3,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 3,0);
        }
      }
;
      public static2(){
        super("static2");
        this.addActionListener(act);
      }
    }
class static3 extends JMenuItem {
      ActionListener act=new ActionListener(){
        public void actionPerformed(        ActionEvent e){
          if (xCoordinate < 0 || xCoordinate >= PopUpMenu.this.model.getPlayground().length - 4) {
            System.err.println("not in range");
            return;
          }
          if (yCoordinate < 0 || yCoordinate >= PopUpMenu.this.model.getPlayground()[0].length - 4) {
            System.err.println("not in range");
            return;
          }
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 2,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 2,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 3,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 3,0);
        }
      }
;
      public static3(){
        super("static3");
        this.addActionListener(act);
      }
    }
class static4 extends JMenuItem {
      ActionListener act=new ActionListener(){
        public void actionPerformed(        ActionEvent e){
          if (xCoordinate < 0 || xCoordinate >= PopUpMenu.this.model.getPlayground().length - 4) {
            System.err.println("not in range");
            return;
          }
          if (yCoordinate < 0 || yCoordinate >= PopUpMenu.this.model.getPlayground()[0].length - 4) {
            System.err.println("not in range");
            return;
          }
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 2,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 2,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 3,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 3,0);
        }
      }
;
      public static4(){
        super("static4");
        this.addActionListener(act);
      }
    }
  }
class PulsatingObjectsMenu extends JMenu {
    public PulsatingObjectsMenu(    String name){
      super(name);
      this.add(new Blinker());
      this.add(new Laser0());
      this.add(new Laser2());
    }
class Laser0 extends JMenuItem {
      ActionListener act=new ActionListener(){
        public void actionPerformed(        ActionEvent e){
          if (xCoordinate < 0 || xCoordinate > PopUpMenu.this.model.getPlayground().length - 4) {
            System.err.println("not in range");
            return;
          }
          if (yCoordinate < 0 || yCoordinate > PopUpMenu.this.model.getPlayground()[0].length - 4) {
            System.err.println("not in range");
            return;
          }
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 2,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 2,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 3,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 3,1);
        }
      }
;
      public Laser0(){
        super("0-Laser");
        this.addActionListener(act);
      }
    }
class Blinker extends JMenuItem {
      ActionListener act=new ActionListener(){
        public void actionPerformed(        ActionEvent e){
          if (xCoordinate < 0 || xCoordinate > PopUpMenu.this.model.getPlayground().length - 3) {
            System.err.println("not in range");
            return;
          }
          if (yCoordinate < 0 || yCoordinate > PopUpMenu.this.model.getPlayground()[0].length - 3) {
            System.err.println("not in range");
            return;
          }
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 2,0);
        }
      }
;
      public Blinker(){
        super("blinker");
        this.addActionListener(act);
      }
    }
class Laser2 extends JMenuItem {
      ActionListener act=new ActionListener(){
        public void actionPerformed(        ActionEvent e){
          if (xCoordinate < 0 || xCoordinate > PopUpMenu.this.model.getPlayground().length - 5) {
            System.err.println("not in range");
            return;
          }
          if (yCoordinate < 0 || yCoordinate > PopUpMenu.this.model.getPlayground()[0].length - 5) {
            System.err.println("not in range");
            return;
          }
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 4,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 4,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 4,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 3,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 4,yCoordinate + 3,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 4,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 4,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 4,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 4,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 4,yCoordinate + 4,1);
        }
      }
;
      public Laser2(){
        super("2-Laser");
        this.addActionListener(act);
      }
    }
  }
class MovingObjectsMenu extends JMenu {
    public MovingObjectsMenu(    String name){
      super(name);
      this.add(new LightWeightSpaceship());
      this.add(new Glider());
    }
class LightWeightSpaceship extends JMenuItem {
      ActionListener act=new ActionListener(){
        public void actionPerformed(        ActionEvent e){
          if (xCoordinate < 0 || xCoordinate > PopUpMenu.this.model.getPlayground().length - 5) {
            System.err.println("not in range");
            return;
          }
          if (yCoordinate < 0 || yCoordinate > PopUpMenu.this.model.getPlayground()[0].length - 5) {
            System.err.println("not in range");
            return;
          }
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 4,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 4,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 2,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 4,yCoordinate + 2,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 3,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 3,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 4,yCoordinate + 3,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 4,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 4,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 4,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 3,yCoordinate + 4,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 4,yCoordinate + 4,0);
        }
      }
;
      public LightWeightSpaceship(){
        super("Segler1");
        this.addActionListener(act);
      }
    }
class Glider extends JMenuItem {
      ActionListener act=new ActionListener(){
        public void actionPerformed(        ActionEvent e){
          if (xCoordinate < 0 || xCoordinate > PopUpMenu.this.model.getPlayground().length - 3) {
            System.err.println("not in range");
            return;
          }
          if (yCoordinate < 0 || yCoordinate > PopUpMenu.this.model.getPlayground()[0].length - 3) {
            System.err.println("not in range");
            return;
          }
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate,0);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 1,0);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 1,1);
          PopUpMenu.this.model.setLifeform(xCoordinate,yCoordinate + 2,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 1,yCoordinate + 2,1);
          PopUpMenu.this.model.setLifeform(xCoordinate + 2,yCoordinate + 2,1);
        }
      }
;
      public Glider(){
        super("Gleiter");
        this.addActionListener(act);
      }
    }
  }
}
