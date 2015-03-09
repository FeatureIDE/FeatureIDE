package de.ovgu.featureide.core.mpl.signature.documentation;

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.mpl.signature.documentation.base.ADocumentationCommentCollector;
import de.ovgu.featureide.core.mpl.signature.documentation.base.SignatureCommentPair;
import de.ovgu.featureide.core.mpl.signature.documentation.base.SignatureCommentPair.Comment;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.abstr.AbstractSignature;
import de.ovgu.featureide.core.signature.abstr.AbstractSignature.FeatureData;
import de.ovgu.featureide.core.signature.filter.IFilter;

public class DocumentationCommentCollector extends ADocumentationCommentCollector<AbstractSignature> {

//	private class FOPCommentIterator implements Iterator<SignatureCommentPair<AbstractSignature>> {
//		private final SignatureIterator sigs;
//		// private int index = 0;
//
//		private SignatureCommentPair<AbstractSignature> next = null;
//
//		public FOPCommentIterator(SignatureIterator sig) {
//			this.sigs = sig;
//		}
//
//		private boolean findNext() {
//			if (sigs.hasNext()) {
//				final AbstractSignature curSignature = sigs.next();
//				final FeatureData[] featureDataArray = curSignature.getFeatureData();
//				final List<Comment> commentList = new LinkedList<>();
//
//				for (int j = 0; j < featureDataArray.length; j++) {
//					final FeatureData featureData = featureDataArray[j];
//					Comment comment = new Comment(featureData.getComment());
//					comment.setFeatureID(featureData.getId());
//					commentList.add(comment);
//				}
//				next = new SignatureCommentPair<AbstractSignature>(curSignature, commentList);
//				return true;
//			}
//			return false;
//		}
//
//		@Override
//		public boolean hasNext() {
//			return (next != null) || findNext();
//		}
//
//		@Override
//		public SignatureCommentPair<AbstractSignature> next() {
//			if (next == null) {
//				findNext();
//			}
//			return next;
//		}
//
//		@Override
//		public void remove() {
//		}
//	}

	public DocumentationCommentCollector(IFeatureProject featureProject) {
		super(featureProject);
	}

	@Override
	public List<SignatureCommentPair<AbstractSignature>> collect(List<IFilter<AbstractSignature>> filters) {
		final FSTModel fstModel = featureProject.getFSTModel();
		if (fstModel != null) {
			final ProjectSignatures projectSignatures = fstModel.getProjectSignatures();
			if (projectSignatures != null) {
				final SignatureIterator it = projectSignatures.iterator();
				for (IFilter<AbstractSignature> filter : filters) {
					it.addFilter(filter);
				}
				// ADocumentationCommentMerger merger = null;

//				int[] featureIDs = new int[projectSignatures.getFeatureCount()];
//				int i = 0;
//				for (String string : featureProject.getFeatureModel().getFeatureOrderList()) {
//					featureIDs[i++] = projectSignatures.getFeatureID(string);
//				}
				
				List<SignatureCommentPair<AbstractSignature>> list = new LinkedList<>();
				
				while (it.hasNext()) {
					final AbstractSignature curSignature = it.next();
					final FeatureData[] featureDataArray = curSignature.getFeatureData();
					final List<Comment> commentList = new LinkedList<>();

					for (int j = 0; j < featureDataArray.length; j++) {
						final FeatureData featureData = featureDataArray[j];
						Comment comment = new Comment(featureData.getComment());
						comment.setFeatureID(featureData.getId());
						commentList.add(comment);
					}
					list.add(new SignatureCommentPair<AbstractSignature>(curSignature, commentList));
				}

				return list;
			}
		}

		return Collections.emptyList();
	}

//	@Override
//	public List<SignatureCommentPair<AbstractSignature>> collect(List<IFilter<AbstractSignature>> filter) {
//		// TODO Auto-generated method stub
//		return null;
//	}

}
