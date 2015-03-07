package de.ovgu.featureide.core.mpl.signature.documentation;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.mpl.signature.documentation.base.ADocumentationCommentCollector;
import de.ovgu.featureide.core.mpl.signature.documentation.base.SignatureCommentPair;
import de.ovgu.featureide.core.mpl.signature.documentation.base.SignatureCommentPair.Comment;
import de.ovgu.featureide.core.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.signature.abstr.AbstractSignature.FeatureData;

public class DocumentationCommentCollector extends ADocumentationCommentCollector<AbstractSignature> {

	private class FOPCommentIterator implements Iterator<SignatureCommentPair<AbstractSignature>> {
		private final AbstractSignature[] sigs;
		private int index = 0;

		private SignatureCommentPair<AbstractSignature> next = null;

		public FOPCommentIterator(AbstractSignature[] sig) {
			this.sigs = sig;
		}

		private boolean findNext() {
			if (index < sigs.length) {
				final AbstractSignature curSignature = sigs[index++];
				final FeatureData[] featureDataArray = curSignature.getFeatureData();
				final List<Comment> commentList = new LinkedList<>();

				for (int j = 0; j < featureDataArray.length; j++) {
					final FeatureData featureData = featureDataArray[j];
					Comment comment = new Comment(featureData.getComment());
					comment.setFeatureID(featureData.getId());
					commentList.add(comment);
				}
				next = new SignatureCommentPair<AbstractSignature>(curSignature, commentList);
				return true;
			}
			return false;
		}

		@Override
		public boolean hasNext() {
			return (next != null) || findNext();
		}

		@Override
		public SignatureCommentPair<AbstractSignature> next() {
			if (next == null) {
				findNext();
			}
			return next;
		}

		@Override
		public void remove() {
		}
	}

	public DocumentationCommentCollector(IFeatureProject featureProject) {
		super(featureProject);
	}

	@Override
	public Iterator<SignatureCommentPair<AbstractSignature>> collect() {
		return new FOPCommentIterator(null);
	}

}
