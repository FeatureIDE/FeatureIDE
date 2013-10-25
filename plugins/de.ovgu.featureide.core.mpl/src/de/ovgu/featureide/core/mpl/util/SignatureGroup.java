package de.ovgu.featureide.core.mpl.util;

import org.eclipse.core.resources.IFolder;

public class SignatureGroup implements Comparable<SignatureGroup> {
	private final int id;
	private final IFolder folder;
	private int size = 0;
	
	public SignatureGroup(int id, IFolder folder) {
		this.id = id;
		this.folder = folder;
	}
	
	public void addSig() {
		size++;
	}

	@Override
	public int compareTo(SignatureGroup otherSigGroup) {
		int dSize = size - otherSigGroup.size;
		return dSize != 0 ? dSize : otherSigGroup.id - id;
	}

	public IFolder getFolder() {
		return folder;
	}
	
	public int getId() {
		return id;
	}
	
	public int size() {
		return size;
	}
}