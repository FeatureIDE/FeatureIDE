import java.awt.BorderLayout;
import java.awt.Button;
import java.awt.Canvas;
import java.awt.Color;
import java.awt.Frame;
import java.awt.Graphics;
import java.awt.Image;
import java.awt.Font;
import java.awt.Toolkit;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.image.ImageObserver;
import java.util.HashMap;
import java.util.Map;
import java.util.Vector;
import java.util.Random;

import javax.swing.JFrame;



abstract class Maler$$PC extends Canvas {

	protected GameManager gameManager;
	protected int GAME_WIDTH;
	protected int GAME_HEIGHT;
	protected Graphics gTemp;
	protected Image offScreenImage;
	protected Menu menu;
	protected JFrame frame;
	protected InfoPanel infoPanel;
	protected int infoWidth;
	public int status;
	protected long time;
	public int tankType = 1;

	protected Toolkit tk = Toolkit.getDefaultToolkit();
	private Random random = new Random();

	public Maler$$PC(GameManager gameManager) {
		this.gameManager = gameManager;
	}

	public void init() {
		gamesize();
		infoPanel = new InfoPanel(((Maler) this));
		infoWidth = InfoPanel.INFO_WIDTH;
		((Maler) this).setSize(GAME_WIDTH + infoWidth, GAME_HEIGHT);
		frame = new JFrame();
		frame.addWindowListener(new WindowAdapter() {
			public void windowClosing(WindowEvent e) {
				System.exit(0);
			}
		});
		frame.add(((Maler) this));
		((Maler) this).setBackground(Color.black);
		frame.setVisible(true);
		frame.setResizable(false);
		frame.addKeyListener(new KeyMonitor(gameManager));
		((Maler) this).addKeyListener(frame.getKeyListeners()[0]);
	}
	
	protected void gamesize(){
		
	}

	public void paint(Graphics g) {
		gTemp = g;
		Color c = g.getColor();
		gameManager.malenkontrolle();
		g.setColor(c);
	}

	public void mainMenu() {
		if (menu == null) {
			mainMenuerstellen();
		}
		menu.erscheinen(gTemp);
	}

	public void mainMenuerstellen() {
		((Maler) this).setSize(GAME_WIDTH + infoWidth, GAME_HEIGHT);
		frame.pack();
		menu = new Menu(((Maler) this));
		menu.add(Sprach.START, 0);
		menu.add(Sprach.HELP, 10);
		menu.add(Sprach.EXIT, 11);
		menu.setStyle(0);
		menu.setKoordinateImage((GAME_WIDTH + infoWidth) / 2, GAME_HEIGHT * 2 / 3);
		menu.setZeileAbstand(0);
		menu.addLogo(loadImage("15.png",(GAME_WIDTH + infoWidth),GAME_HEIGHT));
		menu.setLogoKoordinate(0, 0);
	}
		
	public void tankWaehlen() {
		if (menu == null) {
			tankErstellen();
		}
		menu.erscheinen(gTemp);
	}

	protected void tankErstellen() {
		menu = new Menu(((Maler) this));
		menu.addLogo(loadImage("15.png",(GAME_WIDTH + infoWidth),GAME_HEIGHT));
		menu.setStyle(1);
		menu.setZeileAbstand(0);
		menu.setKoordinateImage((GAME_WIDTH + infoWidth) / 2, GAME_HEIGHT*2/ 3);
		
	}
	
	public void help() {
		if (menu == null) {
			helpItemErstellen();
		}
		menu.erscheinen(gTemp);
	}

	public void helpItemErstellen() {
		menu = new Menu(((Maler) this));
		menu.add(Sprach.HelpItem, loadImage("transparent.png",0,0),loadImage("help.png",0,0), 0);
		menu.setStyle(3);
		menu.setKoordinateImage((GAME_WIDTH + infoWidth) / 2, GAME_HEIGHT / 2);
	}
	
	public Image loadImage(String str, int a, int b) {
		Image tempimage = tk.getImage(Tank.class.getClassLoader().getResource(
				"images/" + str));
		if (a == 0 && b == 0) {
			return tempimage;
		}
		return tempimage.getScaledInstance(a, b, Image.SCALE_FAST);
	}
	
	protected void gameLevel(int lvl) {
		if (menu == null) {
			time = System.currentTimeMillis();
			frame.remove(infoPanel);
			((Maler) this).setSize(GAME_WIDTH + infoWidth, GAME_HEIGHT);
			frame.pack();
			menu = new Menu(((Maler) this));
			menu.setKoordinateImage((GAME_WIDTH + infoWidth) / 2, GAME_HEIGHT / 2);
			menu.setZeileAbstand(0);
			menu.add(Sprach.LEVEL, 0);
			menu.add(lvl + "", 1);
			menu.setWaehlbar(false);
			menu.setFontSize(70);
			menu.setStyle(0);
			menu.setZeileAbstand(55);
		}
		menu.erscheinen(gTemp);
		if (System.currentTimeMillis() - time > 2000) {
			gamescreenstart();
			menu = null;
		}

	}
	
	public void gameLose() {
		if (menu == null) {
			time = System.currentTimeMillis();
			menu = new Menu(((Maler) this));
			menu.setKoordinateImage((GAME_WIDTH + infoWidth) / 2, GAME_HEIGHT / 2);
			menu.setZeileAbstand(0);
			menu.add(Sprach.LOSE, 0);
			menu.setFontSize(70);
			menu.setStyle(0);
			menu.setZeileAbstand(55);
		}
		menu.erscheinen(gTemp);
		if (System.currentTimeMillis() - time > 3000) {
			frame.remove(infoPanel);
			((Maler) this).setSize(GAME_WIDTH + infoWidth, GAME_HEIGHT);
			frame.pack();
			((Maler) this).setStatus(GameManager.MAIN_MENU);
			gameManager.setStatus(gameManager.MAIN_MENU);
			menu = null;
		}

	}
	
	protected void gameWin() {
		if (menu == null) {
			time = System.currentTimeMillis();
			frame.remove(infoPanel);
			((Maler) this).setSize(GAME_WIDTH + infoWidth, GAME_HEIGHT);
			frame.pack();
			menu = new Menu(((Maler) this));
			menu.setKoordinateImage((GAME_WIDTH + infoWidth) / 2, GAME_HEIGHT / 2);
			menu.setZeileAbstand(0);
			menu.add(Sprach.WIN, 0);
			menu.setFontSize(80);
			menu.setStyle(0);
			menu.setZeileAbstand(55);
		}
		menu.erscheinen(gTemp);
		if (System.currentTimeMillis() - time > 3000) {
			((Maler) this).setStatus(GameManager.MAIN_MENU);
			((Maler) this).gameManager.setStatus(GameManager.MAIN_MENU);
			menu = null;
		}

	}
	
	public void gameExit() {
		if (menu == null) {
			frame.remove(infoPanel);
			((Maler) this).setSize(GAME_WIDTH + infoWidth, GAME_HEIGHT);
			frame.pack();
			menu = new Menu(((Maler) this));
			menu.setKoordinateImage((GAME_WIDTH + infoWidth) / 2, GAME_HEIGHT / 2);
			menu.setZeileAbstand(0);
			menu.add(Sprach.MAIN_MENU, 1);
			menu.add(Sprach.RESUME, 0);
			menu.setStyle(0);
			menu.setZeileAbstand(55);
		}
		menu.erscheinen(gTemp);
	}

	private void gamescreenstart() {
		((Maler) this).setStatus(GameManager.SPIELEN);
		((Maler) this).gameManager.setStatus(GameManager.SPIELEN);
		((Maler) this).setSize(GAME_WIDTH, GAME_HEIGHT);
		frame.add(BorderLayout.EAST, ((Maler) this).infoPanel);
		frame.pack();
		menu = null;
	}

	public void pause() {
		if (menu == null) {
			menu = new Menu(((Maler) this));
			menu.setKoordinateImage((GAME_WIDTH + infoWidth) / 2, GAME_HEIGHT / 2);
			menu.setZeileAbstand(0);
			menu.add(Sprach.PAUSE, 0);
			menu.setStyle(0);
			menu.setZeileAbstand(55);
		}
		menu.erscheinen(gTemp);
	}

	public void keyPressedBehandeln(int key) {
		if (menu != null) {
			menu.KeyBehandeln(key);
			//System.out.println(key);
		}
	}

	public void menuBehandeln(String option) {
		//System.out.println(option);
		if (option.equals(Sprach.START)) {
			((Maler) this).setStatus(GameManager.TANK_WAEHLEN);
			((Maler) this).gameManager.setStatus(GameManager.TANK_WAEHLEN);
			menu = null;
		}
		if (option.equals(Sprach.MAIN_MENU)) {
			((Maler) this).setStatus(GameManager.MAIN_MENU);
			((Maler) this).gameManager.setStatus(GameManager.MAIN_MENU);
			menu = null;
		}
		if (option.equals(Sprach.NOTE)) {
			((Maler) this).setStatus(GameManager.NOTE);
			((Maler) this).gameManager.setStatus(GameManager.NOTE);
			menu = null;
		}
		if (option.equals(Sprach.HNOTE)) {
			((Maler) this).setStatus(GameManager.MAIN_MENU);
			((Maler) this).gameManager.setStatus(GameManager.MAIN_MENU);
			menu = null;
		}
		if (option.equals(Sprach.HELP)) {
			((Maler) this).setStatus(GameManager.HELP);
			gameManager.setStatus(GameManager.HELP);
			menu = null;
		}
		if (option.equals(Sprach.HelpItem)) {
			((Maler) this).setStatus(GameManager.MAIN_MENU);
			((Maler) this).gameManager.setStatus(GameManager.MAIN_MENU);
			menu = null;
		}
		if (option.equals(Sprach.EXIT)) {
			System.exit(0);
		}
		if (option.equals(Sprach.PAUSE)) {
			((Maler) this).setStatus(GameManager.SPIELEN);
			((Maler) this).gameManager.setStatus(GameManager.SPIELEN);
			menu = null;
		}
		if (option.equals(Sprach.RESUME)) {
			gamescreenstart();
		}
		if (option.equals(Sprach.TANKA)) {
			menu = null;
			tankType = 01;
			((Maler) this).setStatus(GameManager.LEVEL);
			gameManager.setStatus(GameManager.LEVEL);
		}
		if (option.equals(Sprach.TANKB)) {
			menu = null;
			tankType = 02;
			((Maler) this).setStatus(GameManager.LEVEL);
			gameManager.setStatus(GameManager.LEVEL);
		}
		if (option.equals(Sprach.TANKC)) {
			menu = null;
			tankType = 03;
			((Maler) this).setStatus(GameManager.LEVEL);
			gameManager.setStatus(GameManager.LEVEL);
		}
	}

	public void keyReleased(int key) {
		((Maler) this).repaint();
	}

	public void update(Graphics g) {
		if (offScreenImage == null) {
			offScreenImage = ((Maler) this).createImage(GAME_WIDTH + InfoPanel.INFO_WIDTH, GAME_HEIGHT);
		}
		Graphics gOffScreen = offScreenImage.getGraphics();
		Color c = gOffScreen.getColor();
		gOffScreen.setColor(Color.black);
		gOffScreen.fillRect(0, 0, GAME_WIDTH + InfoPanel.INFO_WIDTH, GAME_HEIGHT);
		gOffScreen.setColor(c);
		paint(gOffScreen);
		g.drawImage(offScreenImage, 0, 0, null);
		infoPanel.repaint();
	}

	public int getScreenWidth() {
		return GAME_WIDTH;
	}

	public int getScreenHeight() {
		return GAME_HEIGHT;
	}

	public void setColor(int R, int G, int B) {
		Color c = new Color(R, G, B);
		gTemp.setColor(c);
	}

	public void setStatus(int status) {
		((Maler) this).status = status;
	}

	public void fillOvall(int x, int y, int width, int height) {
		gTemp.fillOval(x, y, width, height);

	}

	public void fillRect(int x, int y, int width, int height) {
		gTemp.fillRect(x, y, width, height);

	}

	public void drawLine(int x1, int y1, int x2, int y2) {
		gTemp.drawLine(x1, y1, x2, y2);

	}

	public void drawRect(int x, int y, int width, int height) {
		gTemp.drawRect(x, y, width, height);
	}

	public void drawRoundRect(int x, int y, int width, int height, int arcw, int arch) {
		gTemp.drawRoundRect(x, y, width, height, arcw, arch);
	}

	
}

abstract class Maler$$M_240 extends  Maler$$PC  {
	
	protected void gamesize(){
		GAME_WIDTH=240;
		GAME_HEIGHT=240;
	}
      // inherited constructors



	public Maler$$M_240 ( GameManager gameManager ) { super(gameManager); }

}

public class Maler extends  Maler$$M_240  {

	protected void tankErstellen(){
		super.tankErstellen();
		int x, y;
		x = GAME_WIDTH * 2 / 3 / 3;
		y = (int) (2.5 * x);
		menu.add(Sprach.TANKB, loadImage("choice22.png",x,y), loadImage("choice02.png",x,y), 2);	
	}
      // inherited constructors



	public Maler ( GameManager gameManager ) { super(gameManager); }
}