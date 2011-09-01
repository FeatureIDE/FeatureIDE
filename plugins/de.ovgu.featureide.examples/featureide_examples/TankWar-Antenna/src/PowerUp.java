
import java.awt.Color;
import java.awt.Image;
import javax.swing.ImageIcon;

public class PowerUp {

    private int X, Y;
    private int id;
    private Color col;
    private boolean aktiv;
    private Image img;
    private ImageIcon ii1;

    public PowerUp(int given_id, String pp){
        ii1 = new ImageIcon(pp);
        img = ii1.getImage();
        X = 0;
        Y = 0;
        id = given_id;
        aktiv = true;

        if (id==0) col = Color.YELLOW;
        else if (id==1) col = Color.BLUE;
        else if (id==2) col = Color.CYAN;
        else if (id==3) col = Color.DARK_GRAY;
        else if (id==4) col = Color.GRAY;
        else if (id==5) col = Color.GREEN;
        else if (id==6) col = Color.MAGENTA;
        else if (id==7) col = Color.ORANGE;
        else if (id==8) col = Color.RED;
    }

    public String getChange(){
        if (id < 3 && id >= 0) return "HP";
        else if (id >= 3 && id < 6) return "SP";
        else if (id >= 6 && id <= 8) return "BP";
        else return "nothing";
    }

    public int getChangeValue(){
        if (id==0) return 25;
        else if (id==1) return 50;
        else if (id==2) return 100;
        else if (id==3) return 3;
        else if (id==4) return 5;
        else if (id==5) return 10;
        else if (id==6) return 50;
        else if (id==7) return 100;
        else if (id==8) return 200;
        else return 0;
    }

    public Image getImg() {
        return img;
    }

    public void setImg(Image img) {
        this.img = img;
    }

    public boolean isAktiv() {
        return aktiv;
    }

    public void setAktiv(boolean aktiv) {
        this.aktiv = aktiv;
    }

    public Color getCol() {
        return col;
    }

    public int getX() {
        return X;
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
