 // Bewegung - Direkte Direktionseingabe

import java.awt.Rectangle;

public class Schuss { //normal

    private int x, y;
    private float degree;
    private boolean stop, fired;

    public Schuss(int x, int y){
        this.x = x;
        this.y = y;
        degree = 0;
        stop = false;
        fired = false;
    }
    
    public Rectangle getBounds(){
        //return new Rectangle((int)getX()-12, (int)getY()-10, getWidth(), getHeight());
        return new Rectangle(x, y, 5, 5);
    }

    public void move(float deg){
            degree = deg;
            y -= Math.cos(Math.toDegrees(degree)/180*Math.PI) * 5;
            x += Math.sin(Math.toDegrees(degree)/180*Math.PI) * 5;
    }

    public float getDegree() {
        return degree;
    }

    public void setDegree(float degree) {
        this.degree = degree;
    }

    public int getX() {
        return x;
    }

    public void setX(int x) {
        this.x = x;
    }

    public int getY() {
        return y;
    }

    public boolean isFired() {
        return fired;
    }

    public void setFired(boolean fired) {
        this.fired = fired;
    }

    public boolean isStop() {
        return stop;
    }

    public void setStop(boolean stop) {
        this.stop = stop;
    }

    public void setY(int y) {
        this.y = y;
    }


}
