package de.ovgu.featureide.featurehouse.signature.documentation;

import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentParser;

public class DocumentationCommentParser extends ADocumentationCommentParser {

	@Override
	protected void parseHead(String[] parts) {
		final String typeString = parts[0];
		
		// Type
		if (typeString.equals("general")) {
			tagFeatureNode = null;
		} else if (typeString.equals("feature")) {
			tagFeatureNode = getCurFeatureNode();
		} else if (typeString.equals("new")) {
			tagFeatureNode = getCurFeatureNode();
			featureTags.clear();
		} else {
			//warning?
			tagFeatureNode = null;
		}
		
		// Priority
		if (parts.length == 2) {
			try {
				tagPriority = Integer.parseInt(parts[1]);
			} catch (NumberFormatException e) {
				//warning?
				tagPriority = 0;
			}
		} else {
			tagPriority = 0;
		}
	}

}
