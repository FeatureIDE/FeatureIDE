package net.apogames.apogame.game;

import net.gliblybits.bitsengine.utils.BitsLog;

public class ApoGameSolve {

	private boolean bSolved;
	
	private boolean bBreak;
	
	private int count;
	
	public boolean shouldBreak() {
		return bBreak;
	}

	public void setBreak(boolean bBreak) {
		this.bBreak = bBreak;
	}

	public boolean canBeSolved(final int[][] level) {
		this.bSolved = false;
		this.bBreak = false;
		this.count = 0;
		
		this.checkLevel(this.getClone(level));
		
		return this.bSolved;
	}
	
	private void checkLevel(final int[][] level) {
		if (this.isLevelDone(level)) {
			this.bSolved = true;
		}
		if (this.bSolved) {
			return;
		}
		if (this.bBreak) {
			return;
		}
		this.count += 1;
//		BitsLog.d("count", "count: "+count);
		for (int y = 0; y < 8; y++) {
			for (int x = 0; x < level[y].length; x++) {
				if (level[y + 8][x] >= 3) {
					int north = this.isNorthFree(level, x, y);
					if (north > 0) {
//						BitsLog.d("test", level[13][0]+" "+level[14][0]+" "+level[15][0]);
						int[][] clone = this.getClone(level);
						clone[y + 8][x] = (int)(clone[y + 8][x] - 1);
						setNorth(clone, x, y, north);
						this.checkLevel(clone);
						if ((this.bSolved) || (this.bBreak)) {
							return;
						}
//						BitsLog.d("test", level[13][0]+" "+level[14][0]+" "+level[15][0]);
//						this.setNorthBack(level, x, y, north);
//						BitsLog.d("test", level[13][0]+" "+level[14][0]+" "+level[15][0]);
					}
					int east = this.isEastFree(level, x, y);
					if (east > 0) {
//						BitsLog.d("test", "before "+level[15][0]+" "+level[15][1]+" "+level[15][2]);
						int[][] clone = this.getClone(level);
						clone[y + 8][x] = (int)(clone[y + 8][x] - 1);
						setEast(clone, x, y, east);
						this.checkLevel(clone);
						if ((this.bSolved) || (this.bBreak)) {
							return;
						}
//						BitsLog.d("test", "mid "+level[15][0]+" "+level[15][1]+" "+level[15][2]);
//						this.setEastBack(level, x, y, east);
//						BitsLog.d("test", "after "+level[15][0]+" "+level[15][1]+" "+level[15][2]);
					}
					int south = this.isSouthFree(level, x, y);
					if (south > 0) {
						int[][] clone = this.getClone(level);
						clone[y + 8][x] = (int)(clone[y + 8][x] - 1);
						setSouth(clone, x, y, south);
						this.checkLevel(clone);
						if ((this.bSolved) || (this.bBreak)) {
							return;
						}
//						this.setSouthBack(level, x, y, south);
//						BitsLog.d("test", level[13][0]+" "+level[14][0]+" "+level[15][0]);
					}
					int west = this.isWestFree(level, x, y);
					if (west > 0) {
						int[][] clone = this.getClone(level);
						clone[y + 8][x] = (int)(clone[y + 8][x] - 1);
						this.setWest(clone, x, y, west);
						this.checkLevel(clone);
						if ((this.bSolved) || (this.bBreak)) {
							return;
						}
//						this.setWestBack(level, x, y, west);
					}
				}
			}
		}
	}
	
	private int isSouthFree(final int[][] level, final int x, final int y) {
		int i = 1;
		for (int curY = y + 1; curY < 8; curY++) {
			if (level[curY + 8][x] < 2) {
				return i;
			} else {
				i += 1;
			}
		}
		return -1;
	}
	
	private void setSouth(final int[][] level, final int x, final int y, final int south) {
		for (int curY = y + south; curY > y; curY--) {
			level[curY + 8][x] = level[curY + 8 - 1][x];
		}
		level[y + 8][x] = 0;
	}
	
	private void setSouthBack(final int[][] level, final int x, final int y, final int south) {
		for (int curY = y; curY < y + south; curY++) {
			level[curY + 8][x] = level[curY + 8 + 1][x];
		}
		level[y + 8][x] = (int)(level[y + 8][x] + 1);
		level[y + 8 + south][x] = 0;
	}
	
	private int isNorthFree(final int[][] level, final int x, final int y) {
		int i = 1;
		for (int curY = y - 1; curY >= 0; curY--) {
			if (level[curY + 8][x] < 2) {
				return i;
			} else {
				i += 1;
			}
		}
		return -1;
	}
	
	private void setNorth(final int[][] level, final int x, final int y, final int north) {
		for (int curY = y - north; curY < y; curY++) {
			level[curY + 8][x] = level[curY + 8 + 1][x];
		}
		level[y + 8][x] = 0;
	}
	
	private void setNorthBack(final int[][] level, final int x, final int y, final int north) {
		for (int curY = y; curY > y - north; curY--) {
			level[curY + 8][x] = level[curY + 8 - 1][x];
		}
		level[y + 8][x] = (int)(level[y + 8][x] + 1);
		level[y + 8 - north][x] = 0;
	}
	
	private int isWestFree(final int[][] level, final int x, final int y) {
		int i = 1;
		for (int curX = x - 1; curX >= 0; curX--) {
			if (level[y + 8][curX] < 2) {
				return i;
			} else {
				i += 1;
			}
		}
		return -1;
	}
	
	private void setWest(final int[][] level, final int x, final int y, final int west) {
		for (int curX = x - west; curX < x; curX++) {
			level[y + 8][curX] = level[y + 8][curX + 1];
		}
		level[y + 8][x] = 0;
	}
	
	private void setWestBack(final int[][] level, final int x, final int y, final int west) {
		for (int curX = x; curX > x - west; curX--) {
			level[y + 8][curX] = level[y + 8][curX - 1];
		}
		level[y + 8][x] = (int)(level[y + 8][x] + 1);
		level[y + 8][x - west] = 0;
	}
	
	private int isEastFree(final int[][] level, final int x, final int y) {
		int i = 1;
		for (int curX = x + 1; curX < 8; curX++) {
			if (level[y + 8][curX] < 2) {
				return i;
			} else {
				i += 1;
			}
		}
		return -1;
	}
	
	private void setEast(final int[][] level, final int x, final int y, final int east) {
		for (int curX = x + east; curX > x; curX--) {
			level[y + 8][curX] = level[y + 8][curX - 1];
		}
		level[y + 8][x] = 0;
	}
	
	private void setEastBack(final int[][] level, final int x, final int y, final int east) {
		for (int curX = x; curX < x + east; curX++) {
			level[y + 8][curX] = level[y + 8][x + 1];
		}
		level[y + 8][x] = (int)(level[y + 8][x] + 1);
		level[y + 8][x + east] = 0;
	}
	
	private boolean isLevelDone(final int[][] level) {
		for (int y = 0; y < 8; y++) {
			for (int x = 0; x < level[y].length; x++) {
				if ((level[y + 8][x] == 2) && (level[y][x] <= 0)) {
					return false;
				}
				if (((level[y + 8][x] < 2) || (level[y + 8][x] > 2)) && (level[y][x] == 1)) {
					return false;
				}
				if (level[y + 8][x] >= 3) {
					return false;
				}
			}
		}
		return true;
	}
	
	private int[][] getClone(final int[][] copy) {
		int[][] clone = new int[copy.length][copy[0].length];
		for (int y = 0; y < clone.length; y++) {
			for (int x = 0; x < clone[y].length; x++) {
				clone[y][x] = copy[y][x];
			}
		}
		return clone;
	}
}
