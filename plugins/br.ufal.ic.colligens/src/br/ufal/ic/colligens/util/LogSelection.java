package br.ufal.ic.colligens.util;

import org.eclipse.jface.text.ITextSelection;

public class LogSelection implements ITextSelection {

	private int line;
	private int column;
	private int offset;

	public LogSelection(int line, int column, int offset) {
		this.line = line;
		this.column = column;
		this.offset = offset;
	}

	@Override
	public boolean isEmpty() {
		
		return false;
	}

	@Override
	public int getOffset() {
		return offset;
	}

	@Override
	public int getLength() {
		
		return column;
	}

	@Override
	public int getStartLine() {
		
		return line;
	}

	@Override
	public int getEndLine() {
		
		return line+1;
	}

	@Override
	public String getText() {
		
		return null;
	}

}
