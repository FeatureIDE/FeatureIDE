package de.ovgu.featureide.featurehouse.signature.documentation;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.documentation.base.ADocumentationBuilder;
import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentCollector;
import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentParser;

public class DocumentationBuilder extends ADocumentationBuilder {

	public DocumentationBuilder(IFeatureProject featureProject) {
		super(featureProject);
	}

	@Override
	protected ADocumentationCommentCollector getCollector(IFeatureProject featureProject) {
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
