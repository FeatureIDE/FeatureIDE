package net.apogames.apogame.game;

import net.apogames.apogame.ApoGameModel;
import net.apogames.apogame.level.ApoGameLevel;
import net.gliblybits.bitsengine.core.BitsFactory;
import net.gliblybits.bitsengine.core.BitsFont;
import net.gliblybits.bitsengine.core.BitsGame;
import net.gliblybits.bitsengine.render.BitsGraphics;

public class ApoGameMenu extends ApoGameModel {

	public static final String QUIT = "quit";
	public static final String PUZZLE = "puzzle";
	public static final String USERLEVELS = "userlevels";
	public static final String EDITOR = "editor";
	/*if[ApoSnake]*/
	public static final String TITLE = "ApoSnake";
	/*end[ApoSnake]*/
	/*if[ApoDice]*/
	public static final String TITLE = "ApoDice";
	/*end[ApoDice]*/
	
	public static BitsFont font;
	public static BitsFont game_font;
	public static BitsFont title_font;
	
	private float clockRotate;
	
	public ApoGameMenu(ApoGamePanel game) {
		super(game);
	}

	@Override
	public void init() {
		this.loadFonts();
		
		this.getStringWidth().put(ApoGameMenu.QUIT, (int)(ApoGameMenu.font.getLength(ApoGameMenu.QUIT)));
		this.getStringWidth().put(ApoGameMenu.PUZZLE, (int)(ApoGameMenu.font.getLength(ApoGameMenu.PUZZLE)));
		/*if[UserLevels]*/
		this.getStringWidth().put(ApoGameMenu.USERLEVELS, (int)(ApoGameMenu.font.getLength(ApoGameMenu.USERLEVELS)));
		/*end[UserLevels]*/
		/*if[LevelEditor]*/
		this.getStringWidth().put(ApoGameMenu.EDITOR, (int)(ApoGameMenu.font.getLength(ApoGameMenu.EDITOR)));
		/*end[LevelEditor]*/
		this.getStringWidth().put(ApoGameMenu.TITLE, (int)(ApoGameMenu.title_font.getLength(ApoGameMenu.TITLE)));
		
		/*if[UserLevels]*/
		this.setUserlevels();
		/*end[UserLevels]*/
	}
	
	public void onResume() {
		this.loadFonts();
	}
	
	private void loadFonts() {
		ApoGameMenu.font = BitsFactory.getIt().getFont("reprise.ttf", 30);
		ApoGameMenu.title_font = BitsFactory.getIt().getFont("reprise.ttf", 38);
			
		ApoGameMenu.game_font = BitsFactory.getIt().getFont("reprise.ttf", 26);
	}

	@Override
	public void touchedPressed(int x, int y, int finger) {
		
	}

	@Override
	public void touchedReleased(int x, int y, int finger) {
		
	}

	@Override
	public void touchedDragged(int x, int y, int oldX, int oldY, int finger) {
		
	}

	@Override
	public void touchedButton(String function) {
		if (function.equals(ApoGameMenu.QUIT)) {
			this.onBackButtonPressed();
		} else if (function.equals(ApoGameMenu.PUZZLE)) {
			this.getGame().setPuzzleChooser();
		/*if[LevelEditor]*/
		} else if (function.equals(ApoGameMenu.EDITOR)) {
			this.getGame().setEditor(false);
		/*end[LevelEditor]*/
		/*if[UserLevels]*/
		} else if (function.equals(ApoGameMenu.USERLEVELS)) {
			this.getGame().setPuzzleGame(-1, "", true);
		/*end[UserLevels]*/
		}
	}
	
	public void onBackButtonPressed() {
		BitsGame.getIt().finish();
	}
	
	/*if[UserLevels]*/
	public void setUserlevels() {
		this.getGame().getButtons()[2].setVisible(true);
		if (ApoGameLevel.editorLevels == null) {
			this.getGame().getButtons()[2].setVisible(false);
		}
	}
	/*end[UserLevels]*/
	
	@Override
	public void think(int delta) {
		this.clockRotate += delta / 10f;
		if (this.clockRotate >= 360) {
			this.clockRotate -= 360;
		}
	}

	@Override
	public void render(final BitsGraphics g) {
		
		this.getGame().drawString(g, ApoGameMenu.TITLE, 240, 45, ApoGameMenu.title_font, new float[] {1, 1, 1, 1}, new float[] {0, 0, 0, 1});
		
		int number = 1;
		if (this.getGame().getButtons() != null) {
			for (int i = 0; i < this.getGame().getButtons().length; i++) {
				if (this.getGame().getButtons()[i].isBVisible()) {
					int x = (int)(this.getGame().getButtons()[i].getX());
					int y = (int)(this.getGame().getButtons()[i].getY());
					int width = (int)(this.getGame().getButtons()[i].getWidth());
					int height = (int)(this.getGame().getButtons()[i].getHeight());
					
					g.setColor(128, 128, 128, 255);
					g.drawFilledRect(x, y, width, height);
					g.setColor(48f/255f, 48f/255f, 48f/255f, 1.0f);
					g.drawRect(x, y, width, height);
					
					this.getGame().drawString(g, this.getGame().getButtons()[i].getFunction(), x + width/2, y + height/2 - ApoGameMenu.font.mCharCellHeight/2, ApoGameMenu.font);
					
					/*if[ApoSnake]*/
					for (int circle = 0; circle < 2; circle++) {
						x += circle * width;
						
						g.setColor(255, 0, 0, 255);
						if (number == 2) {
							g.setColor(0, 255, 0);
						} else if (number == 3) {
							g.setColor(0, 90, 200);
						} else if (number == 4) {
							g.setColor(255, 255, 0);
						}
						g.drawFilledCircle(x, y + height/2, height/2, height/2);

						g.setLineSize(3.0f);
						g.setColor(48, 48, 48);
						g.drawCircle(x, y + height/2, height/2, height/2);
						
						g.drawFilledRect(x - 5, y + 5, 4, 15);
						g.drawFilledRect(x + 1, y + 5, 4, 15);
						
						g.setLineSize(1.0f);
					}
					/*end[ApoSnake]*/
					/*if[ApoDice]*/
					for (int dice = 0; dice < 2; dice++) {
						x += dice * width;
						
						g.setColor(255, 255, 255, 255);
						g.drawFilledRoundRect(x - height/2, y, height, height, 6, 10);

						g.setLineSize(3.0f);
						g.setColor(48, 48, 48);
						g.drawRoundRect(x - height/2, y, height, height, 6, 10);
						
						g.setLineSize(1.0f);
						
						if ((number == 1) || (number == 3) || (number == 5)) {
							g.drawFilledCircle(x - height/2 + 30, y + 30, 6, 40);
						}
						if ((number == 2) || (number == 3) || (number == 4) || (number == 5)) {
							g.drawFilledCircle(x - height/2 + 14, y + 14, 6, 40);
							g.drawFilledCircle(x - height/2 + 46, y + 46, 6, 40);
						}
						if ((number == 4) || (number == 5)) {
							g.drawFilledCircle(x - height/2 + 46, y + 14, 6, 40);
							g.drawFilledCircle(x - height/2 + 14, y + 46, 6, 40);
						}
					}
					/*end[ApoDice]*/
					number += 1;
				}
			}
		}
	}

}
