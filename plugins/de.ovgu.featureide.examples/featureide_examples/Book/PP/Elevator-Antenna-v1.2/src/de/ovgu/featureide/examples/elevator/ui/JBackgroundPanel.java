package de.ovgu.featureide.examples.elevator.ui;

import java.awt.Graphics;
import java.awt.image.BufferedImage;
import java.io.IOException;
import java.io.InputStream;

import javax.imageio.ImageIO;
import javax.swing.JPanel;

public class JBackgroundPanel extends JPanel {

	private static final long serialVersionUID = 4393744577987449476L;
	private final BufferedImage backgroundImage;

	public JBackgroundPanel(InputStream fileName) throws IOException {
		backgroundImage = ImageIO.read(fileName);
	}

	public void paintComponent(Graphics g) {
		super.paintComponent(g);
		g.drawImage(backgroundImage, 
			(this.getWidth()  - backgroundImage.getWidth() ) / 2,
			(this.getHeight() - backgroundImage.getHeight()) / 2, this);
	}
}