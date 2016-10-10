package net.apogames.apogame.entity;

import net.apogames.apogame.game.ApoGameMenu;
import net.gliblybits.bitsengine.render.BitsGraphics;

public class ApoGameString extends ApoGameEntity {

	public static final int TIME_DECREASE = 10;
	
	private String drawString;
	
	private int invisible;
	
	private int curTime;
	
	private boolean bWithBackground;
	
	private int timeDecrease;
	
	private boolean bFade;
	
	public ApoGameString(float x, float y, float width, String s, boolean bWithBackground, int timeDecrease, boolean bFade) {
		/*if[ApoSnake]*/
		super((int)x, (int)y, (int)width, 0);
		/*end[ApoSnake]*/
		/*if[ApoDice]*/
		super(x, y, width, 0, 0);
		/*end[ApoDice]*/
		
		this.bWithBackground = bWithBackground;
		this.drawString = s;
		this.invisible = 255;
		this.curTime = 0;
		this.timeDecrease = timeDecrease;
		this.curTime = this.timeDecrease;
		this.bFade = bFade;
	}
	
	public void think(int delta) {
		this.curTime -= delta;
		if (this.curTime <= 0) {
			if (this.bFade) {
				this.curTime = this.timeDecrease;
				this.invisible -= 1;
				if (this.invisible <= 50) {
					this.invisible = 0;
					super.setVisible(false);
				}
			} else {
				super.setVisible(false);
			}
		}
	}
	
	public void render(final BitsGraphics g, int changeX, int changeY) {
		if (this.isVisible()) {
			
			String s = this.drawString;
			/*if[ApoSnake]*/
			int w = (int)(ApoGameMenu.font.getLength(s) + 10);
			int h = ApoGameMenu.font.mCharCellHeight;
			int x = (int)(this.getX() + this.getDirection()/2 - w/2) - changeX;
			int change = 10;
			int y = (int)(this.getY() + this.getDirection()/2 + h/2) - changeY;
			/*end[ApoSnake]*/
			/*if[ApoDice]*/
			int w = (int)(ApoGameMenu.font.getLength(s) + 10);
			int h = ApoGameMenu.font.mCharCellHeight;
			int x = (int)(this.getX() + this.getRadius()/2 - w/2) - changeX;
			int change = 10;
			int y = (int)(this.getY() + this.getRadius()/2 + h/2) - changeY;
			/*end[ApoDice]*/
			if (this.bWithBackground) {
				g.setColor(255, 255, 255, this.invisible);
				g.drawFilledRect((int)(x - change), (int)(y - h - change), (int)(w + 2 * change), (int)(h + 2 * change));
				g.setColor(0, 0, 0, this.invisible);
				g.setLineSize(3);
				g.drawRect((int)(x - change), (int)(y - h - change), (int)(w + 2 * change), (int)(h + 2 * change));
				g.setLineSize(1);
			}
			g.setColor(0, 0, 0, this.invisible);
			g.drawText(s, ApoGameMenu.font, x, y - h);
		}
	}

}
