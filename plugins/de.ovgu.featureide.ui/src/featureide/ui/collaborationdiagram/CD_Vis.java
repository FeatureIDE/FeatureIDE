/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide.ui.collaborationdiagram;

import java.awt.Graphics;
import java.util.ArrayList;
import java.util.Iterator;

import javax.swing.JFrame;
import javax.swing.WindowConstants;

/**
 * TODO description Constanze?
 * 
 * @author Janet Feigenspan
 */
public class CD_Vis extends JFrame{

	private static final long serialVersionUID = 1L;
	private CD_Diagram diagram;
	private ArrayList<Collaboration> cols;
	
	private static final int CLASS_WIDTH = 150;
	private static final int CLASS_HEIGHT = 420;
	private static final int CLASS_START_X = 120;
	private static final int CLASS_START_Y = 100;
	private static final int CLASS_DIST = 170;
	
	private static final int COL_WIDTH = 190;
	private static final int COL_HEIGHT = 100;
	private static final int COL_START_X = 100;
	private static final int COL_START_Y = 130;
	private static final int COL_DIST = 130;
	
	public CD_Vis(CD_Diagram diagram) {
		this.diagram = diagram;
		cols = new ArrayList<Collaboration>();
		this.setSize(800, 700);
		this.setTitle("Collaboration Diagram");
		this.setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
		this.setVisible(true);
	}

	public void paint(Graphics g) {
	    super.paint(g);
	    drawCollaborations(g);
	    drawClasses(g);
	}

	private void drawCollaborations(Graphics g) {
		Iterator<CD_Collaboration> iterator = diagram.getCollaborations().iterator();
		int y = COL_START_Y;
		while (iterator.hasNext()) {
			CD_Collaboration col = iterator.next();
			g.drawString(col.getName(), 20, y + 20);
			g.drawRect(COL_START_X, y, COL_WIDTH, COL_HEIGHT);
			cols.add(new Collaboration(y, col.getName()));
			y += COL_DIST;
		}			
	}

	private void drawClasses(Graphics g) {
		Iterator<CD_Class> iterator = diagram.getClasses().iterator();
		int x = CLASS_START_X;
		while (iterator.hasNext()) {
			CD_Class cdClass = iterator.next();
			g.drawString(cdClass.getName(), x, 50);
			g.drawRect(x, CLASS_START_Y, CLASS_WIDTH, CLASS_HEIGHT);
			drawRoles(g, cdClass, x);
			x += CLASS_DIST;
		}
	}

	private void drawRoles(Graphics g, CD_Class cdClass, int x) {
		Iterator<CD_Role> iterator = cdClass.getRoles().iterator();
		while (iterator.hasNext()) {
			CD_Role role = iterator.next();
			String name = role.getName();
			name = name.substring(0, name.indexOf("/"));
			int y = findCollaboration(name).getY();
			g.drawRect(x + 10, y + 30, 130, 60);
			g.drawString(role.getName(), x + 10, y + 20);
		}
	}
	
	private Collaboration findCollaboration(String name) {
		Iterator<Collaboration> iterator = cols.iterator();
		while (iterator.hasNext()) {
			Collaboration col = iterator.next();
			if (col.getName().equals(name))
				return col;
		}
		return null;
		
	}
	
	/**
	 * Saves the name and y-coordinate of a collaboration;
	 * for adding roles to the visualization of the collaboration-diagram
	 * @author yesnice
	 *
	 */
	public class Collaboration {
		private int y;
		private String name;
		public Collaboration (int y, String name) {
			this.setY(y);
			this.setName(name);
		}
		public void setY(int y) {
			this.y = y;
		}
		public int getY() {
			return y;
		}
		public void setName(String name) {
			this.name = name;
		}
		public String getName() {
			return name;
		}
		
	}

}
