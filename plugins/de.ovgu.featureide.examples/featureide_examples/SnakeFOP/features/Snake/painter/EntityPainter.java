package painter;

import java.awt.Graphics;
import java.awt.Image;
import java.awt.image.BufferedImage;

import javax.imageio.ImageIO;

import menu.MyIO;
import basics.field.GameField;
import entitys.Snake;
import entitys.util.EntityHelpings;
import entitys.util.IEntity;
import entitys.util.IEntityPart;

/**
 * Zeichnet Entitäten.
 * 
 * @author Alexander Grebhahn
 * @author Reimar Schröter
 * 
 * @version 1.0
 */
public class EntityPainter {

	// Snake Image Zeilen
	private int snakeHead = 0;
	private int snakeMiddle = 1;
	private int snakeTail = 3;
	
	private void paintSnake(Snake snake) {
		if (!snake.alreadyMoved()) {
			bigPicturePaint(2, snakeMiddle, snake.getHead().getXPos(),
					snake.getHead().getYPos());
		} else {
			for (IEntityPart snakePart : snake) {
				if (snakePart == snake.getHead()) {
					bigPicturePaint(snakePart.getRoute(),
							snakeHead, snakePart.getXPos(),
							snakePart.getYPos());
				} else if (snakePart == snake.getTail()) {
					bigPicturePaint(snakePart.getRoute(),
							snakeTail, snakePart.getXPos(),
							snakePart.getYPos());
				} else {
					int x = snakePart.getStatus() >> 2;
					int y = snakePart.getStatus() % 4;
					bigPicturePaint(y,
							x, snakePart.getXPos(),
							snakePart.getYPos());
				}
			}
		}
	}
}
