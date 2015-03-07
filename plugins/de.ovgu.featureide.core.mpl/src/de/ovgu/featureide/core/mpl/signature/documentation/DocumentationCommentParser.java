package de.ovgu.featureide.core.mpl.signature.documentation;

import de.ovgu.featureide.core.mpl.signature.documentation.base.ADocumentationCommentParser;

public class DocumentationCommentParser extends ADocumentationCommentParser {

	@Override
	protected void parseHead(String[] parts) {
		final String typeString = parts[0];
		
		// Type
		if (typeString.equals("general")) {
			curInfoType = 0;
		} else if (typeString.equals("feature")) {
			curInfoType = 1;
		} else if (typeString.equals("new")) {
			curInfoType = 1;
			featureTags.clear();
		} else {
			//warning?
			curInfoType = 1;
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
