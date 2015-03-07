package de.ovgu.featureide.core.mpl.signature.documentation;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.mpl.signature.documentation.base.ADocumentationBuilder;
import de.ovgu.featureide.core.mpl.signature.documentation.base.ADocumentationCommentCollector;
import de.ovgu.featureide.core.mpl.signature.documentation.base.ADocumentationCommentParser;
import de.ovgu.featureide.core.signature.abstr.AbstractSignature;

public class DocumentationBuilder extends ADocumentationBuilder<AbstractSignature> {

	public DocumentationBuilder(IFeatureProject featureProject) {
		super(featureProject);
	}

	@Override
	protected ADocumentationCommentCollector<AbstractSignature> getCollector(IFeatureProject featureProject) {
		return new DocumentationCommentCollector(featureProject);
	}

	@Override
	protected ADocumentationCommentParser getParser() {
		return new DocumentationCommentParser();
	}

	@Override
	protected void setComment(AbstractSignature signature, String comment) {
		signature.setMergedjavaDocComment(comment);
	}

}
