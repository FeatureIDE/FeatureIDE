/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.examples.utils;

import static de.ovgu.featureide.fm.core.localization.StringTable.REQUIREMENT;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

/**
 * Choosing example description must be loaded through xml file and to be parsed. (@author Constanze Adler)
 *
 * @author Alexander Dreiling
 *
 */
public class CommentParser {

	public static final String OPENTAG_BEGIN = "[";
	public static final String OPENTAG_END = "[/";
	public static final String CLOSETAG = "]";

	public static final String DESCRIPTION_TAG = "description";
	public static final String REQUIREMENT_CATEGORYS_TAG = "requirementcategory";
	public static final String REQUIREMENT_CATEGORY_NAME_TAG = "categoryname";
	public static final String REQUIREMENT_TAG = REQUIREMENT;
	public static final String PLUGIN_ID_TAG = "pluginid";
	public static final String PLUGIN_MISSING_MSG_TAG = "errormsg";

	private final String comment;
	private String desc;
	private final List<RequirementCategory> req = new ArrayList<RequirementCategory>();

	public CommentParser(String comment) {
		this.comment = comment.replaceAll("\n", "").replaceAll("\t", "");
	}

	private String getTextInTag(String tag, String text, int fromIdx) {
		String openTag;
		final int startId = text.indexOf(openTag = (OPENTAG_BEGIN + tag + CLOSETAG), fromIdx);
		final int endId = text.indexOf(OPENTAG_END + tag + CLOSETAG, startId + openTag.length());

		if ((startId < 0) || (endId < 0)) {
			return "";
		}

		return text.substring(startId + openTag.length(), endId);
	}

	private List<String> getElements(String tag, String text, int fromIdx) {
		String openTag;
		final List<String> results = new ArrayList<String>();

		int startId = 0;
		int endId = 0;

		startId = text.indexOf(openTag = (OPENTAG_BEGIN + tag + CLOSETAG), fromIdx);
		endId = text.indexOf(OPENTAG_END + tag + CLOSETAG, startId + openTag.length());

		while ((startId >= 0) && (endId >= 0) && (startId < endId)) {
			results.add(text.substring(startId + openTag.length(), endId));

			fromIdx = endId + 1;

			startId = text.indexOf(openTag = (OPENTAG_BEGIN + tag + CLOSETAG), fromIdx);
			endId = text.indexOf(OPENTAG_END + tag + CLOSETAG, startId + openTag.length());

		}

		return results;
	}

	private String getTextInTag(String tag, String text) {
		return getTextInTag(tag, text, 0);
	}

	public String getDescription() {
		if (desc != null) {
			return desc;
		}

		return desc = getTextInTag(DESCRIPTION_TAG, comment);
	}

	public List<RequirementCategory> getRequirements() {
		if (req.size() > 0) {
			return req;
		}

		// get the requirements
		final List<String> reqCats = getElements(REQUIREMENT_CATEGORYS_TAG, comment, 0);
		final Iterator<String> i = reqCats.iterator();

		String reqGroup;
		String catName;
		String curReq;
		Map<String, String> requirements;

		while (i.hasNext()) {
			reqGroup = i.next();
			catName = getTextInTag(REQUIREMENT_CATEGORY_NAME_TAG, reqGroup);
			requirements = new HashMap<String, String>();
			final List<String> reqs = getElements(REQUIREMENT_TAG, reqGroup, 0);
			final Iterator<String> j = reqs.iterator();

			while (j.hasNext()) {
				curReq = j.next();
				requirements.put(getTextInTag(PLUGIN_ID_TAG, curReq), getTextInTag(PLUGIN_MISSING_MSG_TAG, curReq));

			}
			// create a requirementcategory and add it to the results
			req.add(new RequirementCategory(catName, requirements));

		}

		return req;
	}

}
