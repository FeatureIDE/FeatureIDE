package de.ovgu.featureide.core.mpl.signature.documentation.base;

import java.util.List;

public class SignatureCommentPair<T> {
	
	public static class Comment {
		private final String comment;
		private int featureID = -1;
		
		public Comment(String comment) {
			this.comment = comment;
		}
		
		public int getFeatureID() {
			return featureID;
		}
		
		public void setFeatureID(int featureID) {
			this.featureID = featureID;
		}
		
		public String getComment() {
			return comment;
		}
	}
	
	private final T signature;
	private final List<Comment> comment;
	
	public SignatureCommentPair(T signature, List<Comment> comment) {
		super();
		this.signature = signature;
		this.comment = comment;
	}
	
	public T getSignature() {
		return signature;
	}
	
	public List<Comment> getComment() {
		return comment;
	}
	
}
