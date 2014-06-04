
import java.awt.Image;
import java.awt.Rectangle;
import javax.swing.ImageIcon;

public class Entity {
    private int speed, width, height, bewegungspunkte, center_TP, links_TP, rechts_TP, vorne_TP, hinten_TP, load;
    private double x, y;
    private float degree;
    private boolean up, down, left, right, stop, collision, mo;
    private String picPath;
    private Image img;
    private Proj schuss;
    private String soundEffect_rotate;
    private String soundEffect_go = "";
    private int tp;
    private boolean rocket = false;

    public Entity(int x, int y, String picPath, String sp){
    	this.x = x;
        this.y = y;
        schuss = new Proj();
        this.picPath = picPath;
        ImageIcon ii = new ImageIcon(picPath);
        img = ii.getImage();
        height = ii.getIconHeight();
        width = ii.getIconWidth();
        speed = 2;
        degree = 0;
        up = false;
        down = false;
        left = false;
        right = false;
        collision = false;
        load = 0;
        mo = false;
        center_TP = 250;
        links_TP = 150;
        rechts_TP = 150;
        vorne_TP = 200;
        hinten_TP = 100;
        tp = 100;
        stop = false;
        
        if (sp == "SP1"){
	        //#if (P1_Rot_Beep1) 
//@	        	soundEffect_rotate = "sounds/beep_1.au";
	        //#elif (P1_Rot_Beep2) 
//@	        	soundEffect_rotate = "sounds/beep_2.au";
	        //#elif (P1_Rot_Beep3) 
//@	        	soundEffect_rotate = "sounds/beep_3.au";
	        //#elif (P1_Rot_Bleep1) 
//@	        	soundEffect_rotate = "sounds/bleep_1.au";
	        //#elif (P1_Rot_Buzzer) 
//@	        	soundEffect_rotate = "sounds/buzzer.au";
	        //#elif (P1_Rot_Cash_register) 
	        	soundEffect_rotate = "sounds/cash_register.au";
	        //#elif (P1_Rot_Cork) 
//@	        	soundEffect_rotate = "sounds/cork.au";
	        //#elif (P1_Rot_Game_Win) 
//@	        	soundEffect_rotate = "sounds/game_win.au";
	        //#elif (P1_Rot_Drip) 
//@	        	soundEffect_rotate = "sounds/drip.au";
	        //#elif (P1_Rot_Gorod) 
//@	        	soundEffect_rotate = "sounds/gorod.au";
	        //#elif (P1_Rot_Horn) 
//@	        	soundEffect_rotate = "sounds/horn.au";
	        //#elif (P1_Rot_Laser_Trill) 
//@	        	soundEffect_rotate = "sounds/laser_trill.au";
	        //#elif (P1_Rot_Police_Siren) 
//@	        	soundEffect_rotate = "sounds/police_siren.au";
	        //#elif (P1_Rot_Siren_1) 
//@	        	soundEffect_rotate = "sounds/siren_1.au";
	        //#elif (P1_Rot_Siren_2) 
//@	        	soundEffect_rotate = "sounds/siren_2.au";
	        //#elif (P1_Rot_yes) 
//@	        	soundEffect_rotate = "sounds/yes.au";
	        //#endif
	        
	        //#if (P1_Mov_Beep1) 
//@	        	soundEffect_go = "sounds/beep_1.au";
	        //#elif (P1_Mov_Beep2)
//@	        	soundEffect_go = "sounds/beep_2.au";
	        //#elif (P1_Mov_Beep3) 
//@	        	soundEffect_go = "sounds/beep_3.au";
	        //#elif (P1_Mov_Bleep1) 
//@	        	soundEffect_go = "sounds/bleep_1.au";
	        //#elif (P1_Mov_Buzzer) 
//@	        	soundEffect_go = "sounds/buzzer.au";
	        //#elif (P1_Mov_Cash_Register) 
//@	        	soundEffect_go = "sounds/cash_register.au";
	        //#elif (P1_Mov_Cork) 
//@	        	soundEffect_go = "sounds/cork.au";
	        //#elif (P1_Mov_Game_Win) 
	        	soundEffect_go = "sounds/game_win.au";
	        //#elif (P1_Mov_Drip) 
//@	        	soundEffect_go = "sounds/drip.au";
	        //#elif (P1_Mov_Gorod) 
//@	        	soundEffect_go = "sounds/gorod.au";
	        //#elif (P1_Mov_Horn) 
//@	        	soundEffect_go = "sounds/horn.au";
	        //#elif (P1_Mov_LaserTrill) 
//@	        	soundEffect_go = "sounds/laser_trill.au";
	        //#elif (P1_Mov_Police_Siren) 
//@	        	soundEffect_go = "sounds/police_siren.au";
	        //#elif (P1_Mov_Siren_1) 
//@	        	soundEffect_go = "sounds/siren_1.au";
	        //#elif (P1_Mov_Siren2) 
//@	        	soundEffect_go = "sounds/siren_2.au";
	        //#elif (P1_Mov_yes) 
//@	        	soundEffect_go = "sounds/yes.au";
	        //#endif
	
	        //#if (mov_0)
	            bewegungspunkte = 250;
	        //#elif (mov_1)
//@	            bewegungspunkte = 0;
	        //#elif (mov_2) 
//@	            bewegungspunkte = 250;
	        //#elif (mov_3)
//@	            bewegungspunkte = 0;
	        //#elif (mov_4)
//@	            //  throw new UnsupportedOperationException("Not supported yet.");
	        //#endif
        }
        else if (sp == "SP2"){
	        //#if (P2_Rot_Beep1) 
//@	        	soundEffect_rotate = "sounds/beep_1.au";
	        //#elif (P2_Rot_Beep2) 
//@	        	soundEffect_rotate = "sounds/beep_2.au";
	        //#elif (P2_Rot_Beep3) 
//@	        	soundEffect_rotate = "sounds/beep_3.au";
	        //#elif (P2_Rot_Bleep1) 
//@	        	soundEffect_rotate = "sounds/bleep_1.au";
	        //#elif (P2_Rot_Buzzer) 
//@	        	soundEffect_rotate = "sounds/buzzer.au";
	        //#elif (P2_Rot_Cash_Register) 
//@	        	soundEffect_rotate = "sounds/cash_register.au";
	        //#elif (P2_Rot_Cork) 
//@	        	soundEffect_rotate = "sounds/cork.au";
	        //#elif (P2_Rot_Game_Win) 
//@	        	soundEffect_rotate = "sounds/game_win.au";
	        //#elif (P2_Rot_Drip) 
//@	        	soundEffect_rotate = "sounds/drip.au";
	        //#elif (P2_Rot_Gorod) 
//@	        	soundEffect_rotate = "sounds/gorod.au";
	        //#elif (P2_Rot_Horn) 
//@	        	soundEffect_rotate = "sounds/horn.au";
	        //#elif (P2_Rot_Laser_Trill) 
//@	        	soundEffect_rotate = "sounds/laser_trill.au";
	        //#elif (P2_Rot_Police_Siren) 
	        	soundEffect_rotate = "sounds/police_siren.au";
	        //#elif (P2_Rot_Siren_1) 
//@	        	soundEffect_rotate = "sounds/siren_1.au";
	        //#elif (P2_Rot_Siren_2) 
//@	        	soundEffect_rotate = "sounds/siren_2.au";
	        //#elif (P2_Rot_Yes) 
//@	        	soundEffect_rotate = "sounds/yes.au";
	        //#endif
	        
	        //#if (P2_Mov_Beep1) 
//@	        	soundEffect_go = "sounds/beep_1.au";
	        //#elif (P2_Mov_Beep2)
//@	        	soundEffect_go = "sounds/beep_2.au";
	        //#elif (P2_Mov_Beep3) 
//@	        	soundEffect_go = "sounds/beep_3.au";
	        //#elif (P2_Mov_Bleep1) 
//@	        	soundEffect_go = "sounds/bleep_1.au";
	        //#elif (P2_Mov_Buzzer) 
//@	        	soundEffect_go = "sounds/buzzer.au";
	        //#elif (P2_Mov_Cah_Register) 
//@	        	soundEffect_go = "sounds/cash_register.au";
	        //#elif (P2_Mov_cork) 
	        	soundEffect_go = "sounds/cork.au";
	        //#elif (P2_Mov_Game_Win) 
//@	        	soundEffect_go = "sounds/game_win.au";
	        //#elif (P2_Mov_Drip) 
//@	        	soundEffect_go = "sounds/drip.au";
	        //#elif (P2_Mov_Gorord) 
//@	        	soundEffect_go = "sounds/gorod.au";
	        //#elif (P2_Mov_Horn) 
//@	        	soundEffect_go = "sounds/horn.au";
	        //#elif (P2_Mov_LaserTrill) 
//@	        	soundEffect_go = "sounds/laser_trill.au";
	        //#elif (P2_Mov_Police_Siren) 
//@	        	soundEffect_go = "sounds/police_siren.au";
	        //#elif (P2_Mov_Siren_1) 
//@	        	soundEffect_go = "sounds/siren_1.au";
	        //#elif (P2_Mov_Siren_2) 
//@	        	soundEffect_go = "sounds/siren_2.au";
	        //#elif (P2_Mov_Yes) 
//@	        	soundEffect_go = "sounds/yes.au";
	        //#endif
	
	        //#if (mov_0) 
	            bewegungspunkte = 250;
	        //#elif (mov_1)
//@	            bewegungspunkte = 0;
	        //#elif (mov_2) 
//@	            bewegungspunkte = 250;
	        //#elif (mov_3)
//@	            bewegungspunkte = 0;
	        //#elif (mov_4)
//@	            //  throw new UnsupportedOperationException("Not supported yet.");
	        //#endif
        }
    }

    public boolean isRocket() {
        return rocket;
    }

    public void setRocket(boolean rocket) {
        this.rocket = rocket;
    }

    public boolean isMo() {
        return mo;
    }

    public void setMo(boolean mo) {
        this.mo = mo;
    }

    public Image getImg() {
        return img;
    }

    public boolean isCollision() {
        return collision;
    }

    public void setStop(boolean stop) {
        this.stop = stop;
    }

    public int getBp() {
        return bewegungspunkte;
    }

    public void setLeft(boolean left) {
        this.left = left;
    }

    public void setRight(boolean right) {
        this.right = right;
    }

    public void setDown(boolean down) {
        this.down = down;
    }

    public void setSpeed(int speed) {
        this.speed = speed;
    }

    public int getTp() {
        return tp;
    }

    public void setTp(int tp) {
        this.tp = tp;
    }

    public void setUp(boolean up) {
        this.up = up;
    }

    public int getHeight() {
        return height;
    }

    public int getWidth() {
        return width;
    }

    public double getX() {
        return x;
    }

    public double getY() {
        return y;
    }

    public void setX(double x) {
        this.x = x;
    }

    public void setY(double y) {
        this.y = y;
    }

    public float getDegree() {
        return degree;
    }

    public Proj getSch() {
        return schuss;
    }

    public void setSch(Proj sch) {
        this.schuss = sch;
    }

    public void setCollision(boolean collision) {
        this.collision = collision;
    }

    public void setBp(int bp) {
        this.bewegungspunkte = bp;
    }

    public int getCenter() {
        return center_TP;
    }

    public void setCenter(int center) {
        this.center_TP = center;
    }

    public int getHinten() {
        return hinten_TP;
    }

    public void setHinten(int hinten) {
        this.hinten_TP = hinten;
    }

    public int getLinks() {
        return links_TP;
    }

    public void setLinks(int links) {
        this.links_TP = links;
    }

    public int getRechts() {
        return rechts_TP;
    }

    public void setRechts(int rechts) {
        this.rechts_TP = rechts;
    }

    public int getVorne() {
        return vorne_TP;
    }

    public void setVorne(int vorne) {
        this.vorne_TP = vorne;
    }

    public int getLoad() {
        return load;
    }

    public void setLoad(int load) {
        this.load = load;
    }
    
    public Rectangle getBounds(){
        return new Rectangle((int)getX(), (int)getY(), getWidth(), getHeight());
    }

    public void move(){
        //#if (mov_0)
            if (up && bewegungspunkte > 0 && stop == false){
                y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
                x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
                bewegungspunkte -= 1;
                Snd.music(soundEffect_rotate);

            }
            if (down && bewegungspunkte > 0 && stop == false){
                y += Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
                x -= Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
                bewegungspunkte -= 1;
                Snd.music(soundEffect_rotate);
            }
            if (left && bewegungspunkte > 0 && stop == false){
                degree -= 0.03;
                bewegungspunkte -= 1;
                Snd.music(soundEffect_go);
            }
            if (right&& bewegungspunkte > 0 && stop == false){
                degree += 0.03;
                bewegungspunkte -= 1;
                Snd.music(soundEffect_go);
            }
        //#elif (mov_1)
//@            if (left && stop == false && load != 1){
//@                degree -= 0.03;
//@                Snd.music(soundEffect_rotate);
//@            }
//@            if (right && stop == false && load != 1){
//@                degree += 0.03;
//@                Snd.music(soundEffect_rotate);
//@            }
//@            if (stop == false && load != 1){
//@                setSpeed((int)(Math.ceil(bewegungspunkte*0.02)));
//@                y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                bewegungspunkte = (int)(bewegungspunkte - bewegungspunkte * 0.02);
//@                if (load != 0 && bewegungspunkte != 0) Snd.music(soundEffect_go);
//@            }
        //#elif (mov_2)
//@            if (up && right && bewegungspunkte > 0 && stop == false){
//@                degree = (float)0.8;
//@                bewegungspunkte -= 1;
//@                Snd.music(soundEffect_go);
//@                y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
//@            }
//@            else if (up && left && bewegungspunkte > 0 && stop == false){
//@                degree = (float)-0.8;
//@                bewegungspunkte -= 1;
//@                Snd.music(soundEffect_go);
//@                y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
//@            }
//@            else if (down && right && bewegungspunkte > 0 && stop == false){
//@                degree = (float)2.35;
//@                bewegungspunkte -= 1;
//@                Snd.music(soundEffect_go);
//@                y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
//@            }
//@            else if (down && left && bewegungspunkte > 0 && stop == false){
//@                degree = (float)-2.35;
//@                bewegungspunkte -= 1;
//@                Snd.music(soundEffect_go);
//@                y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
//@            }
//@            else if (up && bewegungspunkte > 0 && stop == false){
//@                degree = (float)0;
//@                bewegungspunkte -= 1;
//@                Snd.music(soundEffect_go);
//@                y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
//@            }
//@            else if(down && bewegungspunkte > 0 && stop == false){
//@                degree = (float)3.15;
//@                bewegungspunkte -= 1;
//@                Snd.music(soundEffect_go);
//@                y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
//@            }
//@            else if(left && bewegungspunkte > 0 && stop == false){
//@                degree = (float)-1.575;
//@                bewegungspunkte -= 1;
//@                Snd.music(soundEffect_go);
//@                y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
//@            }
//@            else if(right && bewegungspunkte > 0 && stop == false){
//@                degree = (float)1.575;
//@                bewegungspunkte -= 1;
//@                Snd.music(soundEffect_go);
//@                y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
//@            }
        //#elif (mov_3)
//@            if (left && stop == false && load == 0){
//@                degree -= 0.03;
//@                Snd.music(soundEffect_rotate);
//@            }
//@            if (right && stop == false && load == 0){
//@                degree += 0.03;
//@                Snd.music(soundEffect_rotate);
//@            }
//@            if (right && stop == false && load == 2 && bewegungspunkte > 0 ){
//@                y -= Math.cos(Math.toDegrees(degree-30)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree-30)/180*Math.PI) * speed;
//@
//@            }
//@            if (left && stop == false && load == 2 && bewegungspunkte > 0 ){
//@                y -= Math.cos(Math.toDegrees(degree+30)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree+30)/180*Math.PI) * speed;
//@            }
//@            if (stop == false && load == 2 && bewegungspunkte > 0 ){
//@                y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                bewegungspunkte = bewegungspunkte - speed;
//@                Snd.music(soundEffect_go);
//@            }
//@            if (stop == false && load != 1){
//@                setSpeed((int)(Math.ceil(bewegungspunkte*0.02)));
//@            }
        //#elif (mov_4)
//@            if (left && stop == false && load == 0){
//@                degree -= 0.03;
//@                Snd.music(soundEffect_rotate);
//@            }
//@            if (right && stop == false && load == 0){
//@                degree += 0.03;
//@                Snd.music(soundEffect_rotate);
//@            }
//@            if (right && stop == false && load == 2){
//@                y -= Math.cos(Math.toDegrees(degree-30)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree-30)/180*Math.PI) * speed;
//@            }
//@            if (left && stop == false && load == 2){
//@                y -= Math.cos(Math.toDegrees(degree+30)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree+30)/180*Math.PI) * speed;
//@            }
//@            if (stop == false && load != 1){
//@                setSpeed((int)(Math.ceil(bewegungspunkte*0.02)));
//@                y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * speed;
//@                bewegungspunkte = (int)(bewegungspunkte - bewegungspunkte * 0.02);
//@                if (load != 0 && bewegungspunkte != 0) Snd.music(soundEffect_go);
//@            }
        //#endif
    }
}
