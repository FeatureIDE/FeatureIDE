package de.ovgu.featureide.antenna.documentation;

import org.prop4j.NodeReader;

import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentParser;

public class DocumentationCommentParser extends ADocumentationCommentParser {

	private final NodeReader nodeReader = new NodeReader();

	@Override
	protected void parseHead(String[] parts) {
		final String typeString = parts[0];
		int prioIndex = 1;
		
		// Type
		if (typeString.equals("general")) {
			tagFeatureNode = null;
		} else if (typeString.equals("feature")) {
			if (parts.length > prioIndex) {
				tagFeatureNode = nodeReader.stringToNode(parts[prioIndex++]);
			} else {
				//warning?
				tagFeatureNode = null;
			}
		} else {
			//warning?
			tagFeatureNode = null;
			tagPriority = 0;
		}
		
		// Priority
		if (parts.length > prioIndex) {
			try {
				tagPriority = Integer.parseInt(parts[prioIndex]);
			} catch (NumberFormatException e) {
				//warning?
				tagPriority = 0;
			}
		} else {
			tagPriority = 0;
		}
	}

}
