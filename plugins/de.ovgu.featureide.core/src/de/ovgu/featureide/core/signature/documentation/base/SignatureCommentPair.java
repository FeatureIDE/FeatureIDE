package de.ovgu.featureide.core.signature.documentation.base;

import java.util.List;

import de.ovgu.featureide.core.signature.base.AbstractSignature;

public class SignatureCommentPair {
	
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
	
	private final AbstractSignature signature;
	private final List<Comment> comment;
	
	public SignatureCommentPair(AbstractSignature signature, List<Comment> comment) {
		super();
		this.signature = signature;
		this.comment = comment;
	}
	
	public AbstractSignature getSignature() {
		return signature;
	}
	
	public List<Comment> getComment() {
		return comment;
	}
	
}
