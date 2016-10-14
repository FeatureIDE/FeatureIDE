package net.apogames.apogame.entity;

import net.gliblybits.bitsengine.render.BitsGraphics;

public class ApoGameEntity {

	/*if[ApoSnake]*/
	private int x, y, direction, color;
	/*end[ApoSnake]*/
	/*if[ApoDice]*/
	private float velocity;
	private float x, y, radius, angle;
	/*end[ApoDice]*/
	
	private boolean bVisible;
	
	/*if[ApoSnake]*/
	public ApoGameEntity(int x, int y, int direction, int color) {
		this.x = x;
		this.y = y;
		this.direction = direction;
		this.color = color;
		this.bVisible = true;
	}

	public int getX() {
		return this.x;
	}

	public void setX(int x) {
		this.x = x;
	}

	public int getY() {
		return this.y;
	}

	public void setY(int y) {
		this.y = y;
	}
	/*end[ApoSnake]*/
	/*if[ApoDice]*/
	public ApoGameEntity(float x, float y, float radius, float angle, float velocity) {
		this.x = x;
		this.y = y;
		this.radius = radius;
		this.angle = angle;
		this.velocity = velocity;
		this.bVisible = true;
	}

	public float getX() {
		return x;
	}

	public void setX(final float x) {
		this.x = x;
	}

	public float getY() {
		return y;
	}

	public void setY(final float y) {
		this.y = y;
	}
	/*end[ApoDice]*/
	
	/*if[ApoSnake]*/
	public int getDirection() {
		return this.direction;
	}

	public void setDirection(int direction) {
		this.direction = direction;
	}

	public int getColor() {
		return this.color;
	}

	public void setColor(int color) {
		this.color = color;
	}
	/*end[ApoSnake]*/
	/*if[ApoDice]*/
	public float getRadius() {
		return radius;
	}

	public void setRadius(final float radius) {
		this.radius = radius;
	}

	public float getAngle() {
		return angle;
	}

	public void setAngle(final float angle) {
		this.angle = angle;
	}

	public float getVelocity() {
		return this.velocity;
	}

	public void setVelocity(final float velocity) {
		this.velocity = velocity;
	}
	/*end[ApoDice]*/
	
	public boolean isVisible() {
		return bVisible;
	}

	public void setVisible(final boolean bVisible) {
		this.bVisible = bVisible;
	}
	
	/*if[ApoDice]*/
	public boolean intersects(final float checkX, final float checkY, final float checkRadius) {
		float newX = (checkX - this.x) * (checkX - this.x);
		float newY = (checkY - this.y) * (checkY - this.y);
		float radius = (checkRadius + this.radius) * (checkRadius + this.radius);
		if (newX + newY <= radius) {
			return true;
		}
		return false;
	}
	/*end[ApoDice]*/
	
	public void think(final int delta) {
		/*if[ApoDice]*/
		this.x += (this.velocity * delta) * Math.sin(Math.toRadians(this.angle));
		this.y += (-this.velocity * delta) * Math.cos(Math.toRadians(this.angle));
		/*end[ApoDice]*/
	}
	
	public void render(final BitsGraphics g) {
		this.render(g, 0, 0);
	}
	
	public void render(final BitsGraphics g, int changeX, int changeY) {
		if (this.isVisible()) {
			/*if[ApoDice]*/
			g.setColor(255f/255f, 120f/255f, 120f/255f, 1.0f);
			g.drawFilledCircle((int)(this.x - changeX), (int)(this.y - changeY), (int)(this.radius), 120);
			g.setColor(0.0f, 0.0f, 0.0f, 1.0f);
			g.drawCircle((int)(this.x - changeX), (int)(this.y - changeY), (int)(this.radius), 120);
			/*end[ApoDice]*/
		}
	}
	
}
