
import java.awt.Image;
import java.awt.Rectangle;
import javax.swing.ImageIcon;

public class Environment {

    private int X, Y;
    private ImageIcon ii1;
    private String picPath;
    private Image img;
    private double degree;

    public Environment(String pic){
        picPath = pic;
        X = 0;
        Y = 0;
        ii1 = new ImageIcon(pic);
        img = ii1.getImage();
        degree = Math.random()*3.6;
    }

    public Rectangle getBounds(){
        return new Rectangle(X, Y, ii1.getIconWidth(), ii1.getIconHeight());
    }

    public double getDegree() {
        return degree;
    }

    public Image getImg() {
        return img;
    }

    public int getX() {
        return X;
    }

    public String getPicPath() {
        return picPath;
    }

    public void setX(int X) {
        this.X = X;
    }

    public int getY() {
        return Y;
    }

    public void setY(int Y) {
        this.Y = Y;
    }

}
