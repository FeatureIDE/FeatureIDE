package de.ovgu.featureide.featurehouse.signature.documentation;

import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentParser;

public class DocumentationCommentParser extends ADocumentationCommentParser {

	@Override
	protected void parseHead(String[] parts) {
		final String typeString = parts[0];
		
		// Type
		if (typeString.equals("general")) {
			tagFeatureID = -1;
		} else if (typeString.equals("feature")) {
			tagFeatureID = curFeatureID;
		} else if (typeString.equals("new")) {
			tagFeatureID = curFeatureID;
			featureTags.clear();
		} else {
			//warning?
			tagFeatureID = -1;
		}
		
		// Priority
		if (parts.length == 2) {
			try {
				curPriority = Integer.parseInt(parts[1]);
			} catch (NumberFormatException e) {
				//warning?
				curPriority = 0;
			}
		} else {
			curPriority = 0;
		}
	}

}
