import java.awt.Color;
import java.awt.Graphics2D;
import java.awt.Image;
import java.awt.Toolkit;
import java.awt.event.*;
import java.awt.geom.AffineTransform;
import java.awt.image.*;
import javax.swing.*;
import javax.imageio.*;
import java.io.*;

public class DrawPanel extends JPanel implements KeyListener, MouseListener, MouseMotionListener{
    /**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	BufferedImage buffer;
    BufferedImage rocketFire = null;
    Schuss sch;
    int timeCounter = 0;
    Entity player_1;
    Entity player_2;
    Entity current_Player;
    Entity other_Player;
    LoadSave ls = new LoadSave();
    Environment env[];
    PowerUp powerUps[];
    int timecount = 0;
    int amountEnv;
    public static int w;
    public static int h;
    public static int[] powerUp_Pic = new int[9];

    public static int kaliber = 5;
    private Image img_bg;
    private ImageIcon ii_bg;

    Graphics2D rkt;

    public DrawPanel(int wth, int hei, int ae){
        amountEnv = ae;
        w = wth;
        h = hei;
        setIgnoreRepaint(true);
        addKeyListener(this);
        addMouseListener(this);
        addMouseMotionListener(this);
        setFocusable(true);
    //    BufferedImage backGr_Img;
    }

    public void initialize(){
        buffer = new BufferedImage(w,h,BufferedImage.TYPE_INT_RGB);
        //#if (Black_P1)
//@        	player_1 = new Entity(100,100, "imgs/Tank_Black.gif", "SP1");
        //#elif (Red_P1) 
//@        	player_1 = new Entity(100,100, "imgs/Tank_Red.gif", "SP1");
        //#elif (Red_Tier1_P1) 
//@        	player_1 = new Entity(100,100, "imgs/Tier1rot.gif", "SP1");
        //#elif (Yellow_Tier1_P1) 
        	player_1 = new Entity(100,100, "imgs/Tier1gelb.gif", "SP1");
        //#elif (Blue_Tier2_P1) 
//@        	player_1 = new Entity(100,100, "imgs/Tier2blau.gif", "SP1");
        //#elif (Green_Tier2_P1) 
//@        	player_1 = new Entity(100,100, "imgs/Tier2gruen.gif", "SP1");
        //#endif

        //#if (Black_P2)
//@        	player_2 = new Entity(200,100, "imgs/Tank_Black.gif", "SP2");
        //#elif (Red_P2) 
//@        	player_2 = new Entity(200,100, "imgs/Tank_Red.gif", "SP2");
        //#elif (Red_Tier1_P2) 
//@        	player_2 = new Entity(200,100, "imgs/Tier1rot.gif", "SP2");
        //#elif (Yellow_Tier1_P2) 
//@        	player_2 = new Entity(200,100, "imgs/Tier1gelb.gif", "SP2");
        //#elif (Blue_Tier2_P2) 
//@        	player_2 = new Entity(200,100, "imgs/Tier2blau.gif", "SP2");
        //#elif (Green_Tier2_P2) 
        	player_2 = new Entity(200,100, "imgs/Tier2gruen.gif", "SP2");
        //#endif
        	
        current_Player = player_1;
        other_Player = player_2;
        env = new Environment[amountEnv];
        powerUps = new PowerUp[9];

        for(int i=0;i<=amountEnv-1;i++){
            //#if (Hinderniss_Set)
//@                if (Math.random()>0.95) env[i] = new Environment("imgs/HindernisseBearbeitet/_b.GIF");
//@                else if (Math.random()>0.90)env[i] = new Environment("imgs/HindernisseBearbeitet/MauerDunkelrot_b.gif");
//@                else if (Math.random()>0.85)env[i] = new Environment("imgs/mauer_hoch.gif");
//@                else if (Math.random()>0.80)env[i] = new Environment("imgs/HindernisseBearbeitet/BaumStamm.gif");
//@                else if (Math.random()>0.75)env[i] = new Environment("imgs/HindernisseBearbeitet/BaumKlein.gif");
//@                else if (Math.random()>0.70)env[i] = new Environment("imgs/HindernisseBearbeitet/BaumKlein_b.GIF");
//@                else if (Math.random()>0.65)env[i] = new Environment("imgs/HindernisseBearbeitet/BaumStamm.gif");
//@                else if (Math.random()>0.60)env[i] = new Environment("imgs/HindernisseBearbeitet/BaumStamm_b.GIF");
//@                else if (Math.random()>0.55)env[i] = new Environment("imgs/HindernisseBearbeitet/MauerDunkelrot_b.gif");
//@                else if (Math.random()>0.50)env[i] = new Environment("imgs/HindernisseBearbeitet/MauerDunkelrot.gif");
//@                else if (Math.random()>0.45)env[i] = new Environment("imgs/HindernisseBearbeitet/MauerDunkelrot_b.GIF");
//@                else if (Math.random()>0.40)env[i] = new Environment("imgs/HindernisseBearbeitet/MauerGrauKurz.gif");
//@                else if (Math.random()>0.35)env[i] = new Environment("imgs/HindernisseBearbeitet/MauerGrauKurz_b.GIF");
//@                else if (Math.random()>0.30)env[i] = new Environment("imgs/HindernisseBearbeitet/MauerGrauKurzDick.gif");
//@                else if (Math.random()>0.25)env[i] = new Environment("imgs/HindernisseBearbeitet/MauerGrauKurzDick_b.GIF");
//@                else if (Math.random()>0.20)env[i] = new Environment("imgs/Haus_vonOben.gif");
//@                else if (Math.random()>0.15)env[i] = new Environment("imgs/HindernisseBearbeitet/MauerGrauLangDick.gif");
//@                else if (Math.random()>0.10)env[i] = new Environment("imgs/HindernisseBearbeitet/MauerGrauLangDick_b.GIF");
//@                else if (Math.random()>0.05)env[i] = new Environment("imgs/HindernisseBearbeitet/MauerRot.gif");
//@                else env[i] = new Environment("imgs/Haus_vonOben_b.GIF");
//@            //}
            //#else
                if (Math.random()>0.75)env[i] = new Environment("imgs/HindernisseBearbeitet/Pfuetze1.gif.gif");
                else if (Math.random()>0.50)env[i] = new Environment("imgs/HindernisseBearbeitet/PfuetzeGross.gif");
                else if (Math.random()>0.25)env[i] = new Environment("imgs/HindernisseBearbeitet/PfuetzeKlein.gif");
                else env[i] = new Environment("imgs/HindernisseBearbeitet/PfuetzeMittel.gif");
        	//#endif
                
            env[i].setX((int)(150 + Math.random()*(w-200)));
            env[i].setY((int)(50 + Math.random()*(h-200)));
        }
        int i = 0;
        while (true) {
	        //#if (Flower)
        	if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpBlume.gif");
	        i++;
        	//#endif
	    	//#if (Blue_Flower)
        	if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpBlumeBlau.gif");
	        i++;
        	//#endif
	    	//#if (Copy)
        	if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpCopy.gif");
	        i++;
        	//#endif
	    	//#if (Fire)
//@        	if (i == 9) break;
	//@    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpFeuer.gif");
	//@        i++;
        	//#endif
	    	//#if (Light_Bulb_Round)
        	if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpGluehbirneRund.gif");
	        i++;
        	//#endif
	    	//#if (Green)
//@        	if (i == 9) break;
	//@    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpGruen.gif");
	//@        i++;
        	//#endif
	    	//#if (Heart)
//@        	if (i == 9) break;
	//@    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpHerz.gif");
	//@        i++;
        	//#endif
	    	//#if (Circle)
//@        	if (i == 9) break;
	//@    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpKreis.gif");
	//@        i++;
        	//#endif
	    	//#if (Cow)
//@        	if (i == 9) break;
	//@    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpKuh.gif");
	//@        i++;
        	//#endif
	    	//#if (Light_Bulb)
        	if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpLightbulb.gif");
	        i++;
        	//#endif
	    	//#if (Octagonal)
//@        	if (i == 9) break;
	//@    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpOctagonal.gif");
	//@        i++;
        	//#endif
	    	//#if (Mushroom)
        	if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpPilz.gif");
	        i++;
        	//#endif
	    	//#if (Pumpkin_Pie)
//@	       if (i == 9) break;
//@	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpPumpkinPie.gif");
//@	        i++;
        	//#endif
	    	//#if (Ring)
	       if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpRing.gif");
	        i++;
        	//#endif
	    	//#if (Ring_2)
	      if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpRingeZwei.gif");
	    	i++;
        	//#endif
	    	//#if (Ring_Oval)
	    if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpRingOval.gif");
	    	i++;
        	//#endif
	    	//#if (Ring_Oval_Small)
	    	if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpRingOvalKlein.gif");
	    	i++;
        	//#endif
	    	//#if (Sponge)
	//@    	if (i == 9) break;
	//@    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpSchwamm.gif");
	//@    	i++;
        	//#endif
	    	//#if (Spiral)
	//@    	if (i == 9) break;
	//@    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpSpiral.gif");
	//@    	i++;
        	//#endif
	    	//#if (Star_Oval)
	    if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpSternOval.gif");
	    	i++;
        	//#endif
	    	//#if (Star_Oval_Small)
	    	if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpSternOvalKlein.gif");
	    	i++;
        	//#endif
	    	//#if (Star_Ring)
	    	if (i == 9) break;
	    	powerUps[i] = new PowerUp(i, "imgs/PowerUpsBearbeitet/PowerUpSternRing.gif");
	    	i++;
	    	//#endif
        }
        //#if (Nr1)
        	powerUps[0].setX(50 + (int)(Math.random()*(w-100)));
            powerUps[0].setY(50 + (int)(Math.random()*(h-150)));
        //#else
//@            powerUps[0].setX(-100);
//@            powerUps[0].setY(-100);
        //#endif
            
          //#if (Nr2)
        	powerUps[1].setX(50 + (int)(Math.random()*(w-100)));
            powerUps[1].setY(50 + (int)(Math.random()*(h-150)));
        //#else
//@            powerUps[1].setX(-100);
//@            powerUps[1].setY(-100);
        //#endif
            
          //#if (Nr3)
        	powerUps[2].setX(50 + (int)(Math.random()*(w-100)));
            powerUps[2].setY(50 + (int)(Math.random()*(h-150)));
        //#else
//@            powerUps[2].setX(-100);
//@            powerUps[2].setY(-100);
        //#endif
        
          //#if (Nr4)
        	powerUps[3].setX(50 + (int)(Math.random()*(w-100)));
            powerUps[3].setY(50 + (int)(Math.random()*(h-150)));
        //#else
//@            powerUps[3].setX(-100);
//@            powerUps[3].setY(-100);
        //#endif
        
          //#if (Nr5)
        	powerUps[4].setX(50 + (int)(Math.random()*(w-100)));
            powerUps[4].setY(50 + (int)(Math.random()*(h-150)));
        //#else
//@            powerUps[4].setX(-100);
//@            powerUps[4].setY(-100);
        //#endif
        
          //#if (Nr6)
        	powerUps[5].setX(50 + (int)(Math.random()*(w-100)));
            powerUps[5].setY(50 + (int)(Math.random()*(h-150)));
        //#else
//@            powerUps[5].setX(-100);
//@            powerUps[5].setY(-100);
        //#endif
        
          //#if (Nr7)
        	powerUps[6].setX(50 + (int)(Math.random()*(w-100)));
            powerUps[6].setY(50 + (int)(Math.random()*(h-150)));
        //#else
//@            powerUps[6].setX(-100);
//@            powerUps[6].setY(-100);
        //#endif
        
          //#if (Nr8)
        	powerUps[7].setX(50 + (int)(Math.random()*(w-100)));
            powerUps[7].setY(50 + (int)(Math.random()*(h-150)));
        //#else
//@            powerUps[7].setX(-100);
//@            powerUps[7].setY(-100);
        //#endif
        
    }

    public void update(){
        current_Player.move();
        //#if (tar)
//@        	// bewegt den Rocket nach Q-Pressed
//@        	if (current_Player.isRocket()){
//@        		sch.move(current_Player.getDegree());
//@        	}
        //#endif
    }

    public void checkCollisions(){
        if (current_Player.getBounds().intersects(other_Player.getBounds()) || current_Player.getBounds().intersects(0, h-50, w, 25) || current_Player.getBounds().intersects(0, 0, w, 25) || current_Player.getBounds().intersects(0, 0, 25, h) || current_Player.getBounds().intersects(w-35, 0, 30, h)){
            current_Player.setCollision(true);
            if (timecount == 0) timecount = 50;
        }
        else
            current_Player.setCollision(false);
    }

    public void checkEnvCollisions(){
        for(int i=0;i<amountEnv;i++){
            //#if (Hinderniss_Set)
//@                if (env[i].getBounds().intersects(current_Player.getBounds())){
//@                    current_Player.setCollision(true);
//@                    if (timecount == 0) timecount = 50;
//@                }
//@            //}
            //#else
                if (env[i].getBounds().intersects(current_Player.getBounds())) current_Player.setSpeed(1);
                //else  current_Player.setSpeed(2);
            //#endif
        }
    }

    public void checkPopupCollision(){
        for(int i=0;i<8;i++){
            if (powerUps[i].isAktiv() && current_Player.getBounds().intersects(powerUps[i].getX(), powerUps[i].getY(), 10, 10)){
                powerUps[i].setAktiv(false);
                if (powerUps[i].getChange().equals("HP")) current_Player.setTp(current_Player.getTp()+powerUps[i].getChangeValue());
                if (powerUps[i].getChange().equals("SP")) current_Player.setSpeed(powerUps[i].getChangeValue());
                if (powerUps[i].getChange().equals("BP")) current_Player.setBp(current_Player.getBp()+powerUps[i].getChangeValue());
            }
        }
    }

    public void drawBuffer(){
        Graphics2D b = buffer.createGraphics(); // DrawPanel
        Graphics2D pl_b = buffer.createGraphics();
        Graphics2D pl_c = buffer.createGraphics();
        rkt = buffer.createGraphics();
        AffineTransform rkt_aff = new AffineTransform();
        Graphics2D envi[] = new Graphics2D[amountEnv];
        AffineTransform enviTrans[] = new AffineTransform[amountEnv];

        b.setColor(Color.BLACK);
        b.fillRect(0, 0, w, h);
        
        //#if (Default)
//@            
        //#elif (Blue_White)
//@        	ii_bg = new ImageIcon("imgs/Hintergrund/HgBlauWeiss1.gif");
//@            img_bg = ii_bg.getImage();
//@            b.drawImage(img_bg, w, w, this);
        //#elif (Blue_White_Green)
//@            ii_bg = new ImageIcon("imgs/Hintergrund/HgBlauWeissGruen.gif");
//@            img_bg = ii_bg.getImage();
//@            b.drawImage(img_bg, w, w, this);
        //#elif (Purple_White)
//@            ii_bg = new ImageIcon("imgs/Hintergrund/HgLilaWeiss.gif");
//@            img_bg = ii_bg.getImage();
//@            b.drawImage(img_bg, w, w, this);
        //#elif (Glass)
//@            ii_bg = new ImageIcon("imgs/Hintergrund/Hintergrundglass05.gif");
//@            img_bg = ii_bg.getImage();
//@            b.drawImage(img_bg, w, w, this);
        //#elif (Lava)
//@            ii_bg = new ImageIcon("imgs/Hintergrund/Hintergrundlava01.gif");
//@            img_bg = ii_bg.getImage();
//@            b.drawImage(img_bg, w, w, this);
        //#elif (Limba)
//@            ii_bg = new ImageIcon("imgs/Hintergrund/Hintergrundlimba.gif");
//@            img_bg = ii_bg.getImage();
//@            b.drawImage(img_bg, w, w, this);
        //#elif (Old)
            ii_bg = new ImageIcon("imgs/Hintergrund/Hintergrundoldpnt01.gif");
            img_bg = ii_bg.getImage();
            b.drawImage(img_bg, w, w, this);
        //#elif (Ov_Paper)
//@            ii_bg = new ImageIcon("imgs/Hintergrund/Hintergrundov_paper.gif");
//@            img_bg = ii_bg.getImage();
//@            b.drawImage(img_bg, w, w, this);
        //#elif (Paper)
//@            ii_bg = new ImageIcon("imgs/Hintergrund/Hintergrundpaper05.gif");
//@            img_bg = ii_bg.getImage();
//@            b.drawImage(img_bg, w, w, this);
        //#elif (Univ)
//@            ii_bg = new ImageIcon("imgs/Hintergrund/Hintergrunduniv01.jpg");
//@            img_bg = ii_bg.getImage();
//@            b.drawImage(img_bg, w, w, this);
        //#elif (Water)
//@            ii_bg = new ImageIcon("imgs/Hintergrund/Hintergrundwater01.jpg");
//@            img_bg = ii_bg.getImage();
//@            b.drawImage(img_bg, w, w, this);
        //#elif (Water_2)
//@            ii_bg = new ImageIcon("imgs/Hintergrund/Hintergrundwater05.jpg");
//@            img_bg = ii_bg.getImage();
//@            b.drawImage(img_bg, w, w, this);
        //#endif
            
        b.setColor(Color.gray);
        b.fillRect(0, 0, w, 25); // oben
        b.fillRect(0, h-50, w, 25); // unten
        b.fillRect(0, 0, 25, h); // links
        b.fillRect(w-35, 0, 30, h); // rechts
        b.setColor(Color.WHITE);

               //rocket
        //#if (tar)
             //#if (Rectangle)
//@               if (current_Player.isRocket()){
//@                   rkt_aff.rotate(current_Player.getDegree(), sch.getX(), sch.getY());
//@                   rkt.setTransform(rkt_aff);
//@                   System.out.println("Rok X:"+sch.getX()+" Rok Y:"+sch.getY());
//@                   rkt.drawRect(sch.getX()+ current_Player.getWidth()/2, sch.getY() + current_Player.getHeight()/2, kaliber, kaliber);} // Rocket 4Eck
             //#endif
             //#if (Oval)
//@               if (current_Player.isRocket()){
//@                   b.drawOval(sch.getX()+ current_Player.getWidth()/2, sch.getY() + current_Player.getHeight()/2, kaliber, kaliber);} // Rocket Oval
        	 //#endif
             //#if (aa31)
//@                 if (current_Player.isRocket()){
//@                     try {
//@                        rocketFire = ImageIO.read(new File("imgs/aa31.gif"));
//@                        rkt_aff.rotate(current_Player.getDegree(), sch.getX(), sch.getY());
//@                        rkt.setTransform(rkt_aff);
//@                        rkt.drawImage(rocketFire, null, (int)sch.getX(), (int)sch.getY());
//@                        //rkt.drawImage(rocketFire, null, (int)current_Player.getX(), (int)current_Player.getY());
//@                    } catch (IOException e) {
//@                    }
//@                 }
              //#endif
              //#if (Portal)
//@                 if (current_Player.isRocket()){
//@                     try {
//@                        rocketFire = ImageIO.read(new File("imgs/portal.gif"));
//@                        rkt_aff.rotate(current_Player.getDegree(), sch.getX(), sch.getY());
//@                        rkt.setTransform(rkt_aff);
//@                        rkt.drawImage(rocketFire, null, sch.getX()+current_Player.getWidth()/2, sch.getY()+current_Player.getHeight()/2);
//@                     } catch (IOException e) {
//@                     }
//@                 }
               //#endif
               //#if (Nino)
//@                 if (current_Player.isRocket()){
//@                     try {
//@                        rocketFire = ImageIO.read(new File("imgs/nino.gif"));
//@                        rkt_aff.rotate(current_Player.getDegree(), sch.getX(), sch.getY());
//@                        rkt.setTransform(rkt_aff);
//@                        rkt.drawImage(rocketFire, null, sch.getX()+current_Player.getWidth()/2, sch.getY()+current_Player.getHeight()/2);
//@                     } catch (IOException e) {
//@                     }
//@                 }
               //#endif
        //#endif
                 
        for(int i=0;i<=amountEnv-1;i++){
            envi[i] = buffer.createGraphics();
            enviTrans[i] = new AffineTransform();
            envi[i].setTransform(enviTrans[i]);
            envi[i].drawImage(env[i].getImg(),env[i].getX(), env[i].getY(), this);
        }
        
        for(int i=0;i<8;i++){
            if (powerUps[i].isAktiv()){
                b.setColor(powerUps[i].getCol());
                b.drawImage(powerUps[i].getImg(),powerUps[i].getX(), powerUps[i].getY(), this);
            }
        }
        
        b.setColor(Color.WHITE);
        b.drawString("BP: " + current_Player.getBp(), 10, 20);
        b.drawString("TP P1/P2: " + player_1.getTp() + " / " + player_2.getTp(), 100, 20);

        if (current_Player.getSch().getEnd_X() != 0 && current_Player.getSch().getEnd_Y() != 0) {
            b.setColor(Color.YELLOW);
            b.drawLine((int)current_Player.getSch().getStart_X(), (int)current_Player.getSch().getStart_Y(), (int)current_Player.getSch().getEnd_X(), (int)current_Player.getSch().getEnd_Y());
            b.setColor(Color.WHITE);
            for (int i=0;i<current_Player.getSch().getArImg().length;i++){
                if (current_Player.getSch().getArImg()[i] != null && current_Player.getSch().isIsActive()){
                    b.drawImage(current_Player.getSch().getArImg()[i],(int)current_Player.getSch().getEnd_X() - current_Player.getSch().getArImg()[i].getWidth(this)/2, (int)current_Player.getSch().getEnd_Y() - current_Player.getSch().getArImg()[i].getHeight(this)/2, (int)(current_Player.getSch().getArImg()[i].getWidth(this)*(current_Player.getSch().getSpeed()/150)), (int)(current_Player.getSch().getArImg()[i].getHeight(this)*(current_Player.getSch().getSpeed()/150)), this);                
                    if (timeCounter == 75){
                        System.out.println("----------------------><---------------------");
                         if (player_1.getBounds().intersects((int)current_Player.getSch().getEnd_X() - current_Player.getSch().getArImg()[i].getWidth(this)/2, (int)current_Player.getSch().getEnd_Y() - current_Player.getSch().getArImg()[i].getHeight(this)/2, (int)(current_Player.getSch().getArImg()[i].getWidth(this)*(current_Player.getSch().getSpeed()/150)), (int)(current_Player.getSch().getArImg()[i].getHeight(this)*(current_Player.getSch().getSpeed()/150)))){
                            player_1.setTp(player_1.getTp()-(int)current_Player.getSch().getSpeed()/4);
                            System.out.println("----------------------> P1 <---------------------");
                        }
                        if (player_2.getBounds().intersects((int)current_Player.getSch().getEnd_X() - current_Player.getSch().getArImg()[i].getWidth(this)/2, (int)current_Player.getSch().getEnd_Y() - current_Player.getSch().getArImg()[i].getHeight(this)/2, (int)(current_Player.getSch().getArImg()[i].getWidth(this)*(current_Player.getSch().getSpeed()/150)), (int)(current_Player.getSch().getArImg()[i].getHeight(this)*(current_Player.getSch().getSpeed()/150)))){
                            player_2.setTp(player_2.getTp()-(int)current_Player.getSch().getSpeed()/4);
                            System.out.println("----------------------> P2 <---------------------");
                        }
                    }
                }
                if (timeCounter >= 150){
                    timeCounter = 0;
                    current_Player.getSch().setIsActive(false);
                    current_Player.getSch().setEnd_X(0);
                    current_Player.getSch().setEnd_Y(0);
                }
                if (current_Player.getSch().isIsActive()) timeCounter += 1;
                System.out.println("timecounter: " + timeCounter);
            }
        }

        if(player_1.getTp()<=0) b.drawString("SPIELER 2 HAT GEWONNEN !", w/2, h/2);
        if(player_2.getTp()<=0) b.drawString("SPIELER 1 HAT GEWONNEN !", w/2, h/2);

        
        current_Player.setStop(false);
        b.setColor(Color.red);

        AffineTransform a = new AffineTransform();
        a.rotate(current_Player.getDegree(), current_Player.getX()+current_Player.getWidth()/2, current_Player.getY()+current_Player.getHeight()/2);
        ((Graphics2D) pl_b).setTransform(a);
        pl_b.drawImage(current_Player.getImg(),(int)current_Player.getX(), (int)current_Player.getY(), this);
        System.out.println("P1 X:"+(int)current_Player.getX()+" P1 Y:"+(int)current_Player.getY());
        System.out.println("P1 W:"+current_Player.getWidth()+" P1 H:"+current_Player.getHeight());
        AffineTransform a2 = new AffineTransform();
        a2.rotate(other_Player.getDegree(), other_Player.getX()+other_Player.getWidth()/2, other_Player.getY()+other_Player.getHeight()/2);
        ((Graphics2D) pl_c).setTransform(a2);
        pl_c.drawImage(other_Player.getImg(),(int)other_Player.getX(), (int)other_Player.getY(), this);
     
        if (current_Player.isCollision() == true){
            current_Player.setStop(true);
            if (timecount > 10) {
                b.setColor(Color.WHITE);
                b.drawString("C O L L I S I O N !", (int)w/2-50, (int)h/2);
                timecount--;
            }
            else{
                timecount = 0;
                current_Player.setBp(0);
                current_Player.setX(300);
                current_Player.setY(100);
                current_Player.getSch().setEnd_X(1);
                current_Player.getSch().setEnd_Y(1);
                current_Player.getSch().setStart_X(1);
                current_Player.getSch().setStart_Y(1);
            }
            b.dispose();
        }
    }

    public void checkRocketCollision(){
        if (current_Player.isRocket()){
            if (current_Player==player_1){
                if(sch.getBounds().intersects(player_2.getBounds())){
                    player_2.setTp(player_2.getTp()-25);
                    current_Player.setRocket(false);
                }
            }
            else if (current_Player==player_2){
                if(sch.getBounds().intersects(player_1.getBounds())){
                    player_1.setTp(player_1.getTp()-25);
                    current_Player.setRocket(false);
                }
            }
            if(sch.getBounds().intersects(0, h-50, w, 25) || sch.getBounds().intersects(0, 0, w, 25) || sch.getBounds().intersects(0, 0, 25, h) || sch.getBounds().intersects(w-35, 0, 30, h)){
                current_Player.setRocket(false);
            }
        }
    }

    public void drawScreen(){
        Graphics2D g = (Graphics2D)this.getGraphics();
        g.drawImage(buffer, 0, 0, this);
        Toolkit.getDefaultToolkit().sync();
        g.dispose();
    }

    public void staga(){
        initialize();
        while(true){
            try{
                update();
                checkCollisions();
                checkPopupCollision();
                checkEnvCollisions();
                checkRocketCollision();
                drawBuffer();
                drawScreen();
                Thread.sleep(15);
            }
            catch(Exception e){
                e.printStackTrace();
            }
        }
    }

    // Bewegung - Normal
    private void changepl() {
       //#if (mov_0)
           current_Player.setBp(250);
           current_Player.getSch().setStart_X(0);
           current_Player.getSch().setStart_Y(0);
           current_Player.getSch().setEnd_X(0);
           current_Player.getSch().setEnd_Y(0);
           current_Player.getSch().setterStart_time(0);
           current_Player.getSch().setterEnd_time(0);
           if (current_Player == player_1){
               current_Player = player_2;
               other_Player = player_1;
           }
           else{
               current_Player = player_1;
               other_Player = player_2;
           }
    	//#endif
       //#if (mov_1)
//@           current_Player.setBp(0);
//@           current_Player.getSch().setStart_X(0);
//@           current_Player.getSch().setStart_Y(0);
//@           current_Player.getSch().setEnd_X(0);
//@           current_Player.getSch().setEnd_Y(0);
//@           current_Player.getSch().setterStart_time(0);
//@           current_Player.getSch().setterEnd_time(0);
//@           current_Player.setLoad(0);
//@           if (current_Player == player_1){
//@               current_Player = player_2;
//@               other_Player = player_1;
//@           }
//@           else{
//@               current_Player = player_1;
//@               other_Player = player_2;
//@           }
         //#endif
       //#if (mov_2)
//@           current_Player.setBp(250);
//@           current_Player.getSch().setStart_X(0);
//@           current_Player.getSch().setStart_Y(0);
//@           current_Player.getSch().setEnd_X(0);
//@           current_Player.getSch().setEnd_Y(0);
//@           current_Player.getSch().setterStart_time(0);
//@           current_Player.getSch().setterEnd_time(0);
//@           if (current_Player == player_1){
//@               current_Player = player_2;
//@               other_Player = player_1;
//@           }
//@           else{
//@               current_Player = player_1;
//@               other_Player = player_2;
//@           }
       //#elif (mov_3)
//@           current_Player.setBp(0);
//@           current_Player.getSch().setStart_X(0);
//@           current_Player.getSch().setStart_Y(0);
//@           current_Player.getSch().setEnd_X(0);
//@           current_Player.getSch().setEnd_Y(0);
//@           current_Player.getSch().setterStart_time(0);
//@           current_Player.getSch().setterEnd_time(0);
//@           current_Player.setLoad(0);
//@           if (current_Player == player_1){
//@               current_Player = player_2;
//@               other_Player = player_1;
//@           }
//@           else{
//@               current_Player = player_1;
//@               other_Player = player_2;
//@           }
       //#elif (mov_4)
//@           current_Player.setBp(0);
//@           current_Player.getSch().setStart_X(0);
//@           current_Player.getSch().setStart_Y(0);
//@           current_Player.getSch().setEnd_X(0);
//@           current_Player.getSch().setEnd_Y(0);
//@           current_Player.getSch().setterStart_time(0);
//@           current_Player.getSch().setterEnd_time(0);
//@           current_Player.setLoad(0);
//@           if (current_Player == player_1){
//@               current_Player = player_2;
//@               other_Player = player_1;
//@           }
//@           else{
//@               current_Player = player_1;
//@               other_Player = player_2;
//@           }
       //#endif
    }

    public void keyPressed(KeyEvent e) {
        //#if (mov_0)
            int key = e.getKeyCode();
            if (key == KeyEvent.VK_LEFT){
                current_Player.setLeft(true);
            }
            if (key == KeyEvent.VK_RIGHT){
                current_Player.setRight(true);
            }
            if (key == KeyEvent.VK_DOWN) current_Player.setDown(true);
            if (key == KeyEvent.VK_UP) current_Player.setUp(true);
            if (key == KeyEvent.VK_SHIFT) current_Player.setSpeed(3);
            if (key == KeyEvent.VK_ENTER) if (current_Player.getSch().isIsActive()==false) changepl();
            if (key == KeyEvent.VK_F1) ls.createNewPlayer();
          //#if (tar)
//@            if (key == KeyEvent.VK_Q){
//@               // current_Player.setRocket(true);
//@               // sch = new Schuss((int)current_Player.getX(),(int)current_Player.getY());
//@               // current_Player.setBp(0);
//@            }
            //#endif
        //#elif (mov_1)
//@            int key = e.getKeyCode();
//@            if (key == KeyEvent.VK_LEFT){
//@                current_Player.setLeft(true);
//@            }
//@            if (key == KeyEvent.VK_RIGHT){
//@                current_Player.setRight(true);
//@            }
//@            if (key == KeyEvent.VK_SPACE && current_Player.getLoad() < 2){
//@                current_Player.setBp(current_Player.getBp()+5);
//@                current_Player.setLoad(1);
//@            }
//@            if (key == KeyEvent.VK_DOWN) current_Player.setDown(true);
//@            if (key == KeyEvent.VK_UP) current_Player.setUp(true);
//@            if (key == KeyEvent.VK_SHIFT) current_Player.setSpeed(3);
//@            if (key == KeyEvent.VK_ENTER) if (current_Player.getSch().isIsActive()==false) changepl();
//@            if (key == KeyEvent.VK_F1) ls.createNewPlayer();
        //#elif (mov_2)
//@            int key = e.getKeyCode();
//@            if (key == KeyEvent.VK_LEFT) current_Player.setLeft(true);
//@            if (key == KeyEvent.VK_RIGHT) current_Player.setRight(true);
//@            if (key == KeyEvent.VK_DOWN) current_Player.setDown(true);
//@            if (key == KeyEvent.VK_UP) current_Player.setUp(true);
//@            if (key == KeyEvent.VK_SHIFT) current_Player.setSpeed(3);
//@            if (key == KeyEvent.VK_ENTER) if (current_Player.getSch().isIsActive()==false) changepl();
//@            if (key == KeyEvent.VK_F1) ls.createNewPlayer();
        //#elif (mov_3)
//@            int key = e.getKeyCode();
//@            if (key == KeyEvent.VK_LEFT){
//@                current_Player.setLeft(true);
//@            }
//@            if (key == KeyEvent.VK_RIGHT){
//@                current_Player.setRight(true);
//@            }
//@            if (key == KeyEvent.VK_SPACE){
//@            	current_Player.setBp(current_Player.getBp()+5);
//@            	current_Player.setLoad(1);
//@                //current_Player.setSpeed(5);
//@            }
//@            if (key == KeyEvent.VK_DOWN) current_Player.setDown(true);
//@            if (key == KeyEvent.VK_UP) current_Player.setUp(true);
//@            if (key == KeyEvent.VK_SHIFT) current_Player.setSpeed(3);
//@            if (key == KeyEvent.VK_ENTER) if (current_Player.getSch().isIsActive()==false) changepl();
//@            if (key == KeyEvent.VK_F1) ls.createNewPlayer();
        //#elif (mov_4)
//@            int key = e.getKeyCode();
//@            if (key == KeyEvent.VK_LEFT){
//@                current_Player.setLeft(true);
//@            }
//@            if (key == KeyEvent.VK_RIGHT){
//@                current_Player.setRight(true);
//@            }
//@            if (key == KeyEvent.VK_SPACE && current_Player.getLoad() < 2){
//@                current_Player.setBp(current_Player.getBp()+5);
//@                current_Player.setLoad(1);
//@            }
//@            if (key == KeyEvent.VK_DOWN) current_Player.setDown(true);
//@            if (key == KeyEvent.VK_UP) current_Player.setUp(true);
//@            if (key == KeyEvent.VK_SHIFT) current_Player.setSpeed(3);
//@            if (key == KeyEvent.VK_ENTER) if (current_Player.getSch().isIsActive()==false) changepl();
//@            if (key == KeyEvent.VK_F1) ls.createNewPlayer();
        //#endif
            
            // neu beginn
            if (key == KeyEvent.VK_Q){
            	//#if (tar)
//@            	current_Player.setRocket(true);
//@            	sch = new Schuss((int)current_Player.getX(),(int)current_Player.getY());
//@            	current_Player.setBp(0);
            	//#endif
            }
            // neu ende
    }

    public void keyReleased(KeyEvent e) {
        //#if (mov_0)
            int key = e.getKeyCode();
            if (key == KeyEvent.VK_LEFT){
                current_Player.setLeft(false);
            }
            if (key == KeyEvent.VK_RIGHT){
                current_Player.setRight(false);
            }
            if (key == KeyEvent.VK_DOWN) current_Player.setDown(false);
            if (key == KeyEvent.VK_UP) current_Player.setUp(false);
            if (key == KeyEvent.VK_SHIFT) current_Player.setSpeed(2);
    	//#endif
        //#if (mov_1)
//@            int key = e.getKeyCode();
//@            if (key == KeyEvent.VK_SPACE && current_Player.getLoad()==1) current_Player.setLoad(2);
//@            if (key == KeyEvent.VK_LEFT) current_Player.setLeft(false);
//@            if (key == KeyEvent.VK_RIGHT) current_Player.setRight(false);
//@            if (key == KeyEvent.VK_DOWN) current_Player.setDown(false);
//@            if (key == KeyEvent.VK_UP) current_Player.setUp(false);
//@            if (key == KeyEvent.VK_SHIFT) current_Player.setSpeed(2);
          //#endif
        //#if (mov_2)
//@            int key = e.getKeyCode();
//@            if (key == KeyEvent.VK_LEFT) current_Player.setLeft(false);
//@            if (key == KeyEvent.VK_RIGHT) current_Player.setRight(false);
//@            if (key == KeyEvent.VK_DOWN) current_Player.setDown(false);
//@            if (key == KeyEvent.VK_UP) current_Player.setUp(false);
//@            if (key == KeyEvent.VK_SHIFT) current_Player.setSpeed(2);
          //#endif
        //#if (mov_3)
//@            int key = e.getKeyCode();
//@            if (key == KeyEvent.VK_SPACE && current_Player.getLoad()==1){current_Player.setLoad(2);}
//@            if (key == KeyEvent.VK_LEFT) current_Player.setLeft(false);
//@            if (key == KeyEvent.VK_RIGHT) current_Player.setRight(false);
//@            if (key == KeyEvent.VK_DOWN) current_Player.setDown(false);
//@            if (key == KeyEvent.VK_UP) current_Player.setUp(false);
//@            if (key == KeyEvent.VK_SHIFT) current_Player.setSpeed(2);
          //#endif
        //#if (mov_4)
//@            int key = e.getKeyCode();
//@            if (key == KeyEvent.VK_SPACE && current_Player.getLoad()==1) current_Player.setLoad(2);
//@            if (key == KeyEvent.VK_LEFT) current_Player.setLeft(false);
//@            if (key == KeyEvent.VK_RIGHT) current_Player.setRight(false);
//@            if (key == KeyEvent.VK_DOWN) current_Player.setDown(false);
//@            if (key == KeyEvent.VK_UP) current_Player.setUp(false);
//@            if (key == KeyEvent.VK_SHIFT) current_Player.setSpeed(2);
        //#endif
    }

    public void keyTyped(KeyEvent e) {
        //#if (mov_0)
            //  throw new UnsupportedOperationException("Not supported yet.");
    	//#endif
        //#if (mov_1)
//@            //  throw new UnsupportedOperationException("Not supported yet.");
    	//#endif
        //#if (mov_2)
//@            //  throw new UnsupportedOperationException("Not supported yet.");
    	//#endif
        //#if (mov_3)
//@            //  throw new UnsupportedOperationException("Not supported yet.");
    	//#endif
        //#if (mov_4)
//@            //  throw new UnsupportedOperationException("Not supported yet.");
        //#endif
    }

    public void mouseClicked(MouseEvent e) {
      //  throw new UnsupportedOperationException("Not supported yet.");
    }

    public void mousePressed(MouseEvent e) {
	     //#if (tar)   
//@    		if (e.getButton() == 1){
//@	            if (current_Player.isMo() && current_Player.getSch().getStart_X() == 0 && current_Player.getSch().isIsActive() == false){
//@	                current_Player.getSch().setIsActive(true);
//@	                current_Player.getSch().setStart_X(e.getX());
//@	                current_Player.getSch().setStart_Y(e.getY());
//@	                current_Player.getSch().setStart_time();
//@	            }
//@	        }
	     //#else
        	if (e.getButton() == 3){
                TankInfo ti = new TankInfo();
                System.out.println("ISIDE");
            }
        //#endif
    }

    public void mouseReleased(MouseEvent e) {
        //#if (tar)
//@	    	if (e.getButton() == 1){
//@	            if (current_Player.getSch().isIsActive() && current_Player.getSch().getEnd_X() == 0){
//@	                current_Player.getSch().setEnd_X(e.getX());
//@	                current_Player.getSch().setEnd_Y(e.getY());
//@	                current_Player.getSch().setEnd_time();
//@	                System.out.println("X " + current_Player.getSch().getStart_X());
//@	                System.out.println("Y " + current_Player.getSch().getStart_Y());
//@	            }
//@	        }
        //#endif
    }

    public void mouseEntered(MouseEvent e) {
    //    throw new UnsupportedOperationException("Not supported yet.");
    }

    public void mouseExited(MouseEvent e) {
      //  throw new UnsupportedOperationException("Not supported yet.");
    }

    public void mouseDragged(MouseEvent e) {
         //  throw new UnsupportedOperationException("Not supported yet.");
    }

    public void mouseMoved(MouseEvent e) {
        //#if (tar)
//@            int mpx = e.getX();
//@            int mpy = e.getY();
//@            if (current_Player.getBounds().contains(mpx, mpy)) current_Player.setMo(true);
//@            else current_Player.setMo(false);
        //#endif
    }

}
