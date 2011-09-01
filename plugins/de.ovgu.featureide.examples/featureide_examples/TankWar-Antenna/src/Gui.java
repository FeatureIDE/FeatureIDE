
import javax.swing.*;

public class Gui {

    JFrame window;
    DrawPanel panel;

    public static int width = 800;
    public static int height = 800;
    
    public static int amoEnv = 3;

    public Gui(){
        if (width < 800) width = 400;
        if (height < 600) height = 400;
        window = new JFrame("TanX");
        panel = new DrawPanel(width, height, amoEnv);
        window.setSize(width, height);
        window.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        window.getContentPane().add(panel);
        window.setVisible(true);
    }

    public void go(){
        panel.staga();
    }

    public static void main(String[] args) {
       Snd.music("game_win.au");
       Gui ga = new Gui();
       ga.go();
    }
}