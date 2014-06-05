

import java.awt.Color; 
import java.awt.Dimension; 
import java.awt.Graphics; 
import java.awt.event.MouseAdapter; 
import java.awt.event.MouseEvent; 
import javax.swing.JPanel; 
import javax.swing.JPopupMenu; 

public  class  PlaygroundPanel  extends JPanel {
	
	private int[][] playground;

	
	private PlaygroundColors myColors=new PlaygroundColors();

	
	private ModelObservable model;

	
	private int xBoxWidth;

	
	private int yBoxWidth;

	
	private int xOffset;

	
	private int yOffset;

	
	public PlaygroundPanel(ModelObservable model, GenerationScheduler sched){
		this.model=model;
		playground=new int[30][30];
		playground= model.getPlayground();
		this.setPreferredSize(new Dimension(700,700));
		this.setBackground(Color.YELLOW);
		this.addMouseListener(new PlaygroundMouseAdapter(this, sched));
	}

	
	public void display(  int[][] playground){
		if (playground.length == 0 || playground[0].length == 0) {
			throw new IllegalArgumentException("leerer Playground");
		}
		this.playground=playground;
		this.repaint();
	}

	
	public void paint(  Graphics g){
		super.paint(g);
		xBoxWidth=(this.getWidth() / playground.length);
		yBoxWidth=(this.getHeight() / playground[0].length);
		xOffset=(this.getWidth() - playground.length * xBoxWidth) / 2;
		yOffset=(this.getHeight() - playground[0].length * yBoxWidth) / 2;
		for (int x=0; x < playground.length; x++) {
			for (int y=0; y < playground[x].length; y++) {
				g.setColor(Color.BLACK);
				g.fillRect(xOffset + (x + 1) * xBoxWidth - 2,yOffset + (y) * yBoxWidth,2,yBoxWidth);
				g.fillRect(xOffset + (x) * xBoxWidth,yOffset + (y + 1) * yBoxWidth - 2,xBoxWidth,2);
				g.setColor(myColors.getColor(playground[x][y]));
				g.fillRect(xOffset + x * xBoxWidth,yOffset + y * yBoxWidth,xBoxWidth - 2,yBoxWidth - 2);
			}
		}
	}

	
	public int getXCoordinate(  int pixel){
		return (pixel - xOffset) / xBoxWidth;
	}

	
	public int getYCoordinate(  int pixel){
		return (pixel - yOffset) / yBoxWidth;
	}

	
	public int getXOffset() {
		return xOffset;
	}

	
	public int getYOffset() {
		return yOffset;
	}

	
	public int getXBoxWidth() {
		return xBoxWidth;
	}

	
	public int getYBoxWidth() {
		return yBoxWidth;
	}

	
	public ModelObservable getModel() {
		return model;
	}

	
	
	public void setFieldOnPlayground(int x, int y, int value) {
		playground[x][y] = value;
		model.setLifeform(x,y,value);
	}

	
	public int getFieldOnPlayground(int x, int y) {
		return playground[x][y];
	}

	
	
	
	static  class  PlaygroundColors1 {
		
		public static Color getColor(    int i){
			switch (i) {
			case (0):
				return Color.BLUE;
			case (1):
				return Color.RED;
			case (2):
				return Color.CYAN;
			case (3):
				return Color.GREEN;
			case (4):
				return Color.ORANGE;
			default :
				return Color.BLACK;
			}
		}


	}

	
	 
	class  PlaygroundColors {
		
		Color[] colors;

		
		public PlaygroundColors(){
			colors=new Color[5];
			colors[0]=new Color(255,240,165);
			colors[1]=new Color(70,137,102);
			colors[2]=new Color(255,176,59);
			colors[3]=new Color(182,73,38);
			colors[4]=new Color(66,71,142);
		}

		
		/**
		 * Default color (dead) is i = 0.
		 * 
		 * @param i
		 * @return
		 */
		public Color getColor(int i){
			return colors[i];
		}


	}


}
