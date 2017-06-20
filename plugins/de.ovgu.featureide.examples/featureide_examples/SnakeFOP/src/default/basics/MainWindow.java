package basics; 

import java.awt.Color; 
import java.awt.TextArea; 
import java.awt.TextField; 
import java.awt.event.ItemEvent; 
import java.awt.event.ItemListener; 
import java.util.Timer; 

import javax.swing.JComboBox; 
import javax.swing.JFrame; 

import menu.MainMenu; 
import painter.Painter; 

import basics.field.GameField; 
import basics.field.Level; 
import basics.util.MyKeyListener; 

import java.util.LinkedList; 
import menu.Highscore; 

public   class  MainWindow  extends JFrame {
	
	private static final long serialVersionUID = 1L;

	
	
	/** Geschwindigkeit, in der das Spiel absolviert wird */
	private static final int[] speed = { 80, 120, 160, 200, 300 };

	
	
	private static final int TEXT = 1, INFO = 2, DIFF = 4, ELEM = 8;

	
	
	public static void main(String[] args) {
		new MainWindow();
	}

	
	
	private final TextField textField = new TextField();

	
	private final TextArea infoTextArea = new TextArea("", 400, 50, TextArea.SCROLLBARS_VERTICAL_ONLY);

	
	private final JComboBox<String> difficultyBox = new JComboBox<String>();

	

	private final JComboBox<Integer> elementSize = new JComboBox<Integer>();

	
	private boolean initMenu = false;

	
	
	private MyKeyListener keyListener = null;

	
	private Timer actionTimer = null;

	
	private GameField level = null;

	

	private Level fieldLevel = null;

	
	/** Anzahl der Leben */
	private int lives = 5;

	

	/** Hauptmenue von dem alles gesteuert wird */
	private final MainMenu mainMenu;

	
	
	private final Painter painter;

	
	
	/**
	 * Eine Application wird gestarted. Alle Menuepunkte werden Vorbereitet.
	 * 
	 * Painter wird geladen ...
	 */
	public MainWindow() {
		setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
		setSize(300, 500);
		setResizable(true);
		setLayout(null);
		setBackground(Color.white);
		setTitle("Snake");
		setFocusable(true);
		
		painter = new Painter(800, 600);

		textField.setEditable(false);
		textField.setFocusable(false);
		textField.setText("Schwierigkeitsgrad");
		textField.setVisible(false);

		difficultyBox.setEditable(false);
		difficultyBox.setBounds(0, 0, 200, 20);
		difficultyBox.addItem("sehr schwer");
		difficultyBox.addItem("schwer");
		difficultyBox.addItem("mittel");
		difficultyBox.addItem("leicht");
		difficultyBox.addItem("sehr leicht");
		difficultyBox.setFocusable(false);
		difficultyBox.setVisible(false);

		elementSize.setEditable(false);
		elementSize.setBounds(0, 0, 200, 20);
		elementSize.addItem(12);
		elementSize.addItem(14);
		elementSize.addItem(16);
		elementSize.addItem(18);
		elementSize.setFocusable(false);
		elementSize.setVisible(true);
		elementSize.addItemListener(new ItemListener() {
			public void itemStateChanged(ItemEvent arg0) {
				MainWindow.this.repaint();
				if (level != null) {
					level.repaint();
				}
			}
		});

		infoTextArea.setEditable(false);
		infoTextArea.setFocusable(false);
		infoTextArea.setVisible(false);
		infoTextArea.setText("Um das Spiel zu starten gehen sie durch das Menu und bet�tigen Sie die Enter-Taste");

		add(infoTextArea).setBounds(0, 0, 400, 50);
		add(textField).setBounds(0, 0, 200, 20);
		add(difficultyBox).setBounds(0, 20, 200, 20);
		add(elementSize).setBounds(0, 20, 200, 20);
		
		mainMenu = new MainMenu(this);
		
		keyListener = new MyKeyListener();
		this.addKeyListener(keyListener);

		this.setVisible(true);
		this.startMainMenu();
	}

	

	/**
	 * 
	 * Verl�sst die Application.
	 */
	public void exit() {
		System.exit(0);
	}

	

	/**
	 * @return Anzahl der Elemente
	 */
	public int getElementSize() {
		return (int) elementSize.getSelectedItem();
	}

	

	/**
	 * @return Anzahl der Leben
	 */
	public int getLives() {
		return lives;
	}

	

	public Painter getPainter() {
		return painter;
	}

	

	/**
	 * Startet Men� Impressum
	 */
	public void impressum() {
		infoTextArea.setText("Entwickelt von:\nAlexander Grebhahn\nReimar Schr�ter");
		setVisibility(INFO);
	}

	

	/**
	 * Startet das n�chste Level, oder beendet das Spiel wenn kein Level
	 * vorhanden ist.
	 * 
	 * @param nextLevel
	 *            gibt an ob die Schlange gestorben ist und das n�chste Level
	 *            gestartet werden soll (nextLevel==false -so wird das gleiche
	 *            Level aufgerufen)
	 */
	public void runningNextLevel(boolean nextLevel) {
		stopAction();

		if (level != null) {
			remove(level);
			level = null;
		}
		fieldLevel = null;

		if (!nextLevel) {
			--lives;
		}

		if (lives == 0 || nameLevel.isEmpty()) {
			gameover();
		} else {
			if (nextLevel) {
				levelName = nameLevel.poll();
			}
			fieldLevel = new Level("/level/" + levelName + ".dat", true);
			fieldLevel.resizeField(2);

			// erzeugt neues GameField aus dem Spielfeld

			level = new GameField(this, fieldLevel);

			add(level).setBounds(0, 50, 800, 600);
			keyListener.setListener(level);
			mainMenu.setVisible(false);
			this.repaint();

			// erzeugt eine Action die das spiel steuert, unterbricht
			// sie und �bergibt das zu steuernde GameField

			startAction();
		}
	}

	
	
	/**{@feature 0}
	 * Testet ob die aktuelle Punktzahl ein Highscore ist und leitet alles weitere ein.
	 */
	private void gameover  () {
		points += lives * 1000;
		startMainMenu();
		if (highscore.setNewHighscore(getDifficulty(), points)) {
			startHighscore();
		}
	}

	

	/**
	 * Geht in den Pausenmodus.
	 *
	 * @param running
	 */
	public void setBreak(boolean running) {
		if (running) {
			startAction();
		} else {
			stopAction();
		}
	}

	

	/**
	 * Startet das eigentliche Spiel.
	 */
	/**{@feature 0}
	 * Setzt die Leben auf 5.
	 */
	 private void  startGame__wrappee__SnakeFOP  () {
		setVisibility(ELEM);
		
		lives = 5;
		runningNextLevel(true);
	}

	

	/**{@feature 0}
	 * Setzt die Punktzahl auf 0.
	 */
	 private void  startGame__wrappee__Points  () {
		points = 0;
		startGame__wrappee__SnakeFOP();
	}

	
	
	/**{@feature 0}
	 * L�dt die Levelnamen.
	 */
	public void startGame() {
		addLevelNames();
		startGame__wrappee__Points();
	}

	

	/**
	 * Startet Men� Highscore
	 */
	public void startInstruction() {
		infoTextArea.setText(
				  "Das Ziel dieses Spieles ist es, alle 10 auftauchenden Tierchen vollst�ndig zu fressen."
				+ " Dabei sollte man auf unwegsames Gel�nde und auf seinen Schlangenschwanz achten. Nachdem alle Tierchen gefressen wurden,"
				+ " muss die Schlange wieder zum Loch gesteuert werden um das n�chste Level erreichen zu k�nnen. Bevor nicht alle Tierchen"
				+ " gefressen wurden, kann die Schlange nicht wieder im Loch verschwinden.\n"
				+ " Die Steuerung der Schlange kann mit Ihren Pfeil-Tasten erfolgen. Um in den Pausenmodus zu gelangen, kann die Enter-Taste oder die P-Taste benutzt werden. Die verschiedenen"
				+ " Schwierigkeitsgrade k�nnen in dem Bereich"
				+ " Einstellungen ver�ndert werden.");
		setVisibility(INFO);
	}

	

	/**
	 * Startet das Hauptmen�.
	 */
	public void startMainMenu() {
		keyListener.setListener(mainMenu);
		if (!initMenu) {
			initMenu = true;
			add(mainMenu).setBounds(0, 50, 600, 600);
		}
		mainMenu.setVisible(true);
		this.repaint();
	}

	
	
	/**
	 * Startet Men� Einstellung
	 */
	public void startSettings() {
		setVisibility(TEXT | DIFF);
	}

	

	private int getDifficulty() {
		return difficultyBox.getSelectedIndex();
	}

	

	private void setVisibility(int flags) {
		textField.setVisible((flags & TEXT) > 0);
		infoTextArea.setVisible((flags & INFO) > 0);
		difficultyBox.setVisible((flags & DIFF) > 0);
		elementSize.setVisible((flags & ELEM) > 0);
		this.repaint();
	}

	
	
	private void startAction() {
		actionTimer = new Timer();
		actionTimer.schedule(new MoveAction(level), 0, speed[getDifficulty()]);
		actionTimer.schedule(new RepaintAction(level), 0, 40);
	}

	

	private void stopAction() {
		if (actionTimer != null) {
			actionTimer.cancel();
		}
	}

	
	private int points = 0;

	

	/**
	 * Setzt eine neue Punktzahl.
	 * 
	 * @param points Punktzahl, die gesetzt werden soll
	 */
	public void addPoints(int points) {
		this.points += points;
	}

	

	/**
	 * Gibt die aktuelle Punktzahl zur�ck.
	 * 
	 * @return die aktuelle Punktzahl
	 */
	public int getPoints() {
		return points;
	}

	
	/** Namen der Level, die in dem Spiel existieren  */
	private static final LinkedList<String> nameLevel = new LinkedList<String>();

	
	
	/**
	 * F�gt neue Level hinzu.
	 */
	/**{@feature 0}
	 * Hook method.
	 */
	 private static void  addLevelNames__wrappee__Level  () {}

	
	/**{@feature 1}
	 * Level 1
	 */
	private static void addLevelNames() {
		addLevelNames__wrappee__Level();
		nameLevel.add("level1");
	}

	

	private String levelName = null;

	
	private final Highscore highscore = new Highscore();

	
	
	/**
	 * Startet das Highscore-Men�.
	 */
	public void startHighscore() {
		infoTextArea.setText(highscore.getHighscoreFromDifficult(getDifficulty()));
		setVisibility(INFO);
	}


}
