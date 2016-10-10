package net.apogames.apogame.game;

import net.apogames.apogame.ApoGame;
import net.apogames.apogame.ApoGameModel;
import net.apogames.apogame.entity.ApoLevelChooserButton;
import net.apogames.apogame.level.ApoGameLevel;
import net.gliblybits.bitsengine.render.BitsGraphics;

public class ApoGamePuzzleChooser extends ApoGameModel {

	public static final String BACK = "back";
	/*if[ApoSnake]*/
	public static final String LEVEL_CHOOSER = "ApoSnake - Levelchooser";
	/*end[ApoSnake]*/
	/*if[ApoDice]*/
	public static final String LEVEL_CHOOSER = "ApoDice - Levelchooser";
	/*end[ApoDice]*/
	
	private ApoLevelChooserButton[] levels;
	
	private int solved = 0;
	
	private int curShow = 0;
	
	public ApoGamePuzzleChooser(ApoGamePanel game) {
		super(game);
	}

	@Override
	public void init() {
		this.getStringWidth().put(ApoGamePuzzleChooser.BACK, (int)(ApoGameMenu.font.getLength(ApoGamePuzzleChooser.BACK)));
		this.getStringWidth().put(ApoGamePuzzleChooser.LEVEL_CHOOSER, (int)(ApoGameMenu.title_font.getLength(ApoGamePuzzleChooser.LEVEL_CHOOSER)));
		
		this.curShow = 0;
		
		if (this.levels == null) {
			this.levels = new ApoLevelChooserButton[ApoGameLevel.MAX_LEVELS];
			
			int xPos = 20;
			int yPos = 50;
			int radius = 70;
			int add = 20;
			int curLevel = 0;
			
			final int lines = ApoGameLevel.MAX_LEVELS / 5;
			for (int y = 0; y < lines; y++) {
				for (int x = 0; x < 5; x++) {
					this.levels[curLevel] = new ApoLevelChooserButton(null, xPos, yPos, radius, radius, String.valueOf(curLevel + 1));
					
					xPos += radius + add;
					curLevel += 1;
					if (curLevel >= this.levels.length) {
						break;
					}
				}
				xPos = 20;
				yPos += radius + add;
				if (curLevel >= this.levels.length) {
					break;
				}
				if (curLevel % 30 == 0) {
					yPos = 70;
				}
			}
			this.setSolved(0);
		}
	}
	
	public final int getSolved() {
		return this.solved;
	}

	public final void setSolved(int solved) {
		if (this.solved < solved) {
			this.solved = solved;
			if (this.solved > ApoGameLevel.MAX_LEVELS - 1) {
				this.solved = ApoGameLevel.MAX_LEVELS - 1;
			}
			if (this.solved < this.levels.length) {
				for (int i = 0; i < this.solved && i < this.levels.length; i++) {
					this.levels[i].setSolved(true);
				}
			}
			this.getGame().savePreferences(ApoGame.settings);
		}
	}	

	@Override
	public void touchedPressed(int x, int y, int finger) {
		if (this.levels != null) {
			for (int i = this.curShow; i < this.curShow + 64 && i < this.levels.length && i <= this.solved; i++) {
				if (this.levels[i].intersects(x, y)) {
					this.getGame().setPuzzleGame(i, "", false);
				}
			}
		}
	}

	@Override
	public void touchedReleased(int x, int y, int finger) {
		
	}

	@Override
	public void touchedDragged(int x, int y, int oldX, int oldY, int finger) {
		
	}

	@Override
	public void touchedButton(String function) {
		if (function.equals(ApoGamePuzzleChooser.BACK)) {
			this.onBackButtonPressed();
		}
	}
	
	public void onBackButtonPressed() {
		this.getGame().setMenu();
	}

	@Override
	public void think(int delta) {
		
	}

	@Override
	public void render(BitsGraphics g) {
		this.getGame().drawString(g, ApoGamePuzzleChooser.LEVEL_CHOOSER, 240, 2, ApoGameMenu.title_font, new float[] {1, 1, 1, 1}, new float[] {0, 0, 0, 1});
		
		this.getGame().renderButtons(g);
		
		if (this.levels != null) {
			for (int i = this.curShow; i < this.curShow + 64 && i < this.levels.length; i++) {
				int x = (int)(this.levels[i].getX());
				int y = (int)(this.levels[i].getY());
				int radius = (int)(this.levels[i].getWidth());
				
				g.setColor(255, 255, 255, 255);
				if (this.levels[i].isSolved()) {
					g.setColor(102, 135, 89, 255);
				} else if (this.solved < i) {
					g.setColor(128, 128, 128, 255);
				}
				/*if[ApoSnake]*/
				g.drawFilledCircle(x + radius/2, y + radius/2, radius/2, 120);

				g.setLineSize(2.5f);
				g.setColor(48, 48, 48);
				g.drawCircle(x + radius/2, y + radius/2, radius/2, 120);
				g.drawFilledRect(x + radius/2 - 4, y + 10, 3, 6);
				g.drawFilledRect(x + radius/2 + 1, y + 10, 3, 6);
				/*end[ApoSnake]*/
				/*if[ApoDice]*/
				g.drawFilledRoundRect(x, y, radius, radius, 6, 10);

				g.setLineSize(2.5f);
				g.setColor(48, 48, 48);
				g.drawRoundRect(x, y, radius, radius, 6, 10);
				/*end[ApoDice]*/
				
				if (this.solved == i) {
					this.getGame().drawString(g, this.levels[i].getFunction(), x + radius/2 - (int)ApoGameMenu.font.getLength(this.levels[i].getFunction())/2, y + radius/2 - ApoGameMenu.font.mCharCellHeight/2, ApoGameMenu.font, new float[] {1, 1, 1, 1}, new float[] {0, 0, 0, 1});
				} else {
					this.getGame().drawString(g, this.levels[i].getFunction(), x + radius/2 - (int)ApoGameMenu.font.getLength(this.levels[i].getFunction())/2, y + radius/2 - ApoGameMenu.font.mCharCellHeight/2, ApoGameMenu.font);
				}
				
				g.setLineSize(1.0f);
			}
		}
	}

}
