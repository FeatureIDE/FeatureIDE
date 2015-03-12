package de.ovgu.featureide.munge.documentation;

import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentCollector;
import de.ovgu.featureide.core.signature.documentation.base.SignatureCommentPair;
import de.ovgu.featureide.core.signature.documentation.base.SignatureCommentPair.Comment;
import de.ovgu.featureide.core.signature.filter.IFilter;

public class DocumentationCommentCollector extends ADocumentationCommentCollector {

	public DocumentationCommentCollector(IFeatureProject featureProject) {
		super(featureProject);
	}
	
	@Override
	public List<SignatureCommentPair> collect(List<IFilter<AbstractSignature>> filters) {
		final ProjectSignatures projectSignatures = new ProjectSignatures(featureProject.getFeatureModel());
		
		final SignatureIterator it = projectSignatures.iterator();
		for (IFilter<AbstractSignature> filter : filters) {
			it.addFilter(filter);
		}
		
		final List<SignatureCommentPair> list = new LinkedList<>();
		
		while (it.hasNext()) {
			final AbstractSignature curSignature = it.next();
			final AFeatureData featureData = curSignature.getFirstFeatureData();
			final List<Comment> commentList = new LinkedList<>();
			Comment comment = new Comment(featureData.getComment());
			commentList.add(comment);
		}

		return list;
	}

}
