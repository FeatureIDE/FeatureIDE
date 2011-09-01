
import java.awt.Image;
import javax.swing.ImageIcon;

public class Proj {

    private int start_X, start_Y, end_X, end_Y;
    private double len, start_time, end_time, speed;
    private Image arImg[];
    private boolean isActive, hit_Player_1, hit_Player_2;

    public Proj(){
        start_X = 0;
        start_Y = 0;
        end_X = 0;
        end_Y = 0;
        start_time = 0;
        end_time = 0;
        len = 0;
        speed = 0;
        isActive = false;
        hit_Player_1 = false;
        hit_Player_2 = false;
        ImageIcon ii1 = new ImageIcon("imgs/explo1.gif");
        ImageIcon ii2 = new ImageIcon("imgs/explo2.gif");
        arImg = new Image[2];
        arImg[0] = ii1.getImage();
        arImg[1] = ii2.getImage();
    }

    public Image[] getArImg() {
        return arImg;
    }

    public double getLen(){
        len = (int)(Math.sqrt(Math.pow(start_X - end_X, 2) + Math.pow(start_Y - end_Y, 2)));
        return len;
    }

    public double getSpeed(){
        speed = (getLen()*100/(end_time - start_time));
        return speed;
    }

    public boolean isIsActive() {
        return isActive;
    }

    public void setIsActive(boolean isActive) {
        this.isActive = isActive;
    }

    public void setLen(double len) {
        this.len = len;
    }

    public double getEnd_X() {
        return end_X;
    }

    public void setEnd_X(int end_X) {
        this.end_X = end_X;
    }

    public int getEnd_Y() {
        return end_Y;
    }

    public void setEnd_Y(int end_Y) {
        this.end_Y = end_Y;
    }

    public int getStart_X() {
        return start_X;
    }

    public void setStart_X(int start_X) {
        this.start_X = start_X;
    }

    public int getStart_Y() {
        return start_Y;
    }

    public void setStart_Y(int start_Y) {
        this.start_Y = start_Y;
    }

    public void setEnd_time() {
        this.end_time = System.currentTimeMillis();
    }

    public void setStart_time() {
        this.start_time = System.currentTimeMillis();
    }

    public double getEnd_time() {
        return end_time;
    }

    public double getStart_time() {
        return start_time;
    }

    public void setterEnd_time(double end_time) {
        this.end_time = end_time;
    }

    public void setterStart_time(double start_time) {
        this.start_time = start_time;
    }

    public void setSpeed(double speed) {
        this.speed = speed;
    }

    public boolean isHiten() {
        return hit_Player_2;
    }

    public void setHiten(boolean hiten) {
        this.hit_Player_2 = hiten;
    }

    public boolean isHitpl() {
        return hit_Player_1;
    }

    public void setHitpl(boolean hitpl) {
        this.hit_Player_1 = hitpl;
    }

}
