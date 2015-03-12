package de.ovgu.featureide.munge.documentation;

import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentParser;

public class DocumentationCommentParser extends ADocumentationCommentParser {

	@Override
	protected void parseHead(String[] parts) {
		final String typeString = parts[0];
		int prioIndex = 1;
		
		// Type
		if (typeString.equals("general")) {
			tagFeatureID = -1;
		} else if (typeString.equals("feature")) {
			tagFeatureID = curFeatureID;
			if (parts.length > prioIndex) {
				final String featureName = parts[prioIndex++];
				// TODO ...
			}
		} else {
			//warning?
			tagFeatureID = -1;
			curPriority = 0;
		}
		
		// Priority
		if (parts.length > prioIndex) {
			try {
				curPriority = Integer.parseInt(parts[prioIndex]);
			} catch (NumberFormatException e) {
				//warning?
				curPriority = 0;
			}
		} else {
			curPriority = 0;
		}
	}

}
