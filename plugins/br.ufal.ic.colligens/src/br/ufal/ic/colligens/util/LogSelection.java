package br.ufal.ic.colligens.util;

import org.eclipse.jface.text.ITextSelection;

public class LogSelection implements ITextSelection {

	private final int line;
	private final int length;
	private final int offset;

	public LogSelection(int line, int length, int offset) {
		this.line = line;
		this.length = length;
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
		return length;
	}

	@Override
	public int getStartLine() {

		return line;
	}

	@Override
	public int getEndLine() {

		return line;
	}

	@Override
	public String getText() {

		return null;
	}

}
