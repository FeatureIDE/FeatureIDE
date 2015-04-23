package de.ovgu.featureide.munge.documentation;

import org.prop4j.NodeReader;

import de.ovgu.featureide.core.signature.documentation.base.ADocumentationCommentParser;

public class DocumentationCommentParser extends ADocumentationCommentParser {

	private final NodeReader nodeReader = new NodeReader();

	@Override
	protected void parseHead(String[] parts) {
		final String typeString = parts[0];

		boolean featureHead = false;
		// Type
		if (typeString.equals("general")) {
			tagFeatureNode = null;
		} else if (typeString.equals("feature")) {
			featureHead = true;
		} else {
			//warning?
			tagFeatureNode = null;
			tagPriority = 0;
		}

		// Priority
		if (parts.length > 1) {
			try {
				tagPriority = Integer.parseInt(parts[parts.length - 1]);
				if (featureHead) {
					if (parts.length > 2) {
						final StringBuilder sb = new StringBuilder();
						for (int i = 1; i < parts.length - 1; i++) {
							sb.append(parts[i]);
							sb.append(' ');
						}
						tagFeatureNode = nodeReader.stringToNode(sb.toString());
					} else {
						//warning?
						tagFeatureNode = null;
					}
				}
			} catch (NumberFormatException e) {
				tagPriority = 0;

				if (featureHead) {
					final StringBuilder sb = new StringBuilder();
					for (int i = 1; i < parts.length; i++) {
						sb.append(parts[i]);
						sb.append(' ');
					}
					tagFeatureNode = nodeReader.stringToNode(sb.toString());
				}
			}
		} else {
			tagPriority = 0;
		}
	}

	@Override
	public boolean addExtraFilters() {
		return true;
	}

}
