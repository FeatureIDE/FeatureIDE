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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;

/**
 * Simple syntax highlighted editor
 *
 * @author Marcus Pinnecke
 */
public class SimpleSyntaxHighlightEditor extends StyledText {

	private final String[] keywords;
	private final Set<String> possibleWords = new HashSet<String>();
	private final Set<String> unknownWords = new HashSet<String>();

	/**
	 * @param parent
	 * @param style
	 */
	public SimpleSyntaxHighlightEditor(Composite parent, int style, final String[] keywords) {
		super(parent, style);
		this.keywords = keywords;

		keywordColor = Display.getDefault().getSystemColor(SWT.COLOR_DARK_RED);
		wrongWordColor = Display.getDefault().getSystemColor(SWT.COLOR_RED);
		normalColor = Display.getDefault().getSystemColor(SWT.COLOR_BLACK);
		setFont(JFaceResources.getTextFont());

		super.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				updateHighlight();
			}
		});
	}

	private final Color keywordColor;
	private final Color wrongWordColor;
	private final Color normalColor;
	private boolean underlineEverything;

	public Set<String> getUnknownWords() {
		return unknownWords;
	}

	public void setPossibleWords(Set<String> words) {
		possibleWords.clear();

		for (final String word : words) {
			possibleWords.add(word);
			possibleWords.add("\"" + word + "\"");
		}

		for (int i = 0; i < keywords.length; i++) {
			final String keyword = keywords[i].toLowerCase();
			possibleWords.add(keyword);
		}
	}

	private void updateHighlight() {
		if (!underlineEverything) {
			final String text = super.getText();

			final StyleRange resetStyleRange = new StyleRange();
			resetStyleRange.start = 0;
			resetStyleRange.length = text.length();
			resetStyleRange.fontStyle = SWT.NORMAL;
			resetStyleRange.foreground = normalColor;
			setStyleRange(resetStyleRange);

			hightlightKeywords(text);
			hightlightWrongWords(text);
		}
	}

	/**
	 * @param text
	 */
	private void hightlightWrongWords(String text) {

		unknownWords.clear();

		for (int i = 0; i < keywords.length; i++) {
			possibleWords.add(keywords[i]);
		}

		String safeCopy = new String(text);
		safeCopy = safeCopy.replace("(", " ").replace(")", " ");

		final StringBuilder safeCopySb = new StringBuilder(safeCopy);

		final char ILLEGAL_FEATURE_NAME_CHAR = '\u0000';
		// avoid splitting feature names with containing spaces by replace spaces inside brackets with a char
		// that could never be inside a feature name and recode this later
		boolean insideFeatureNameWithWhitespace = false;
		for (int i = 0; i < safeCopy.length(); i++) {
			if (safeCopy.charAt(i) == '\"') {
				insideFeatureNameWithWhitespace = !insideFeatureNameWithWhitespace;
			}
			if (insideFeatureNameWithWhitespace && (safeCopy.charAt(i) == ' ')) {
				safeCopySb.replace(i, i + 1, String.valueOf(ILLEGAL_FEATURE_NAME_CHAR));
			}
		}

		final String[] tokens = safeCopySb.toString().split(" ");
		int start = 0;
		for (int i = 0; i < tokens.length; i++) {
			final String token = tokens[i].trim().replace(ILLEGAL_FEATURE_NAME_CHAR, ' ');

			if (!token.isEmpty() && !possibleWords.contains(token) && !possibleWords.contains(token.toLowerCase())) {
				unknownWords.add(token);

				final StyleRange styleRange = new StyleRange();
				styleRange.start = start;
				styleRange.length = token.length();
				styleRange.underlineStyle = SWT.UNDERLINE_ERROR;
				styleRange.underline = true;
				styleRange.underlineColor = wrongWordColor;
				styleRange.foreground = normalColor;

				setStyleRange(styleRange);
			}
			start += tokens[i].length() + 1;
		}
	}

	private static class Match {

		private final int start, end;

		public Match(int start, int end) {
			this.start = start;
			this.end = end;
		}
	}

	private static final Pattern nonOperators = Pattern.compile("\"[^\"]*\"");

	private void hightlightKeywords(String text) {
		final List<Match> keywordPositions = new ArrayList<>();

		final StringBuilder sb = new StringBuilder("(");
		for (final String keyword : keywords) {
			sb.append(Pattern.quote(keyword.toLowerCase()));
			sb.append('|');
		}
		sb.setCharAt(sb.length() - 1, ')');

		final Matcher operatorMatcher = Pattern.compile(sb.toString()).matcher(text);
		final Matcher nonOperatorMatcher = nonOperators.matcher(text);

		Match nonOperatorMatch = null;
		if (nonOperatorMatcher.find()) {
			nonOperatorMatch = new Match(nonOperatorMatcher.start(), nonOperatorMatcher.end());
		}
		while (operatorMatcher.find()) {
			final int start = operatorMatcher.start();
			final int end = operatorMatcher.end();

			while ((nonOperatorMatch != null) && (start > nonOperatorMatch.end)) {
				if (nonOperatorMatcher.find()) {
					nonOperatorMatch = new Match(nonOperatorMatcher.start(), nonOperatorMatcher.end());
				} else {
					nonOperatorMatch = null;
				}
			}
			if ((nonOperatorMatch == null) || !((start < nonOperatorMatch.end) && (end > nonOperatorMatch.start))) {
				keywordPositions.add(new Match(start, end));
			}
		}

		// highlight keywords in text
		for (final Match match : keywordPositions) {
			final StyleRange styleRange = new StyleRange();
			styleRange.start = match.start;
			styleRange.length = match.end - match.start;
			styleRange.fontStyle = SWT.BOLD;
			styleRange.foreground = keywordColor;

			setStyleRange(styleRange);
		}
	}

	public void copyIn(final String textToInsert) {
		final StringBuilder temp = new StringBuilder(super.getText());

		final int selStart = super.getSelectionRanges()[0];
		final int selLen = super.getSelectionRanges()[1];

		if (selLen != 0) {
			temp.delete(selStart, selStart + selLen);
		}

		String prefix = "";
		if ((selStart - 1) > 0) {
			prefix += temp.charAt(selStart - 1) == ' ' ? "" : " ";
		}
		String suffix = "";
		final int lastIndex = selStart + prefix.length() + textToInsert.length();
		suffix += lastIndex >= temp.length() ? " " : (temp.charAt(lastIndex) == ' ' ? "" : " ");

		temp.insert(selStart, prefix + textToInsert + suffix);
		super.setText(temp.toString());
		super.setFocus();
		super.setSelection(selStart + prefix.length() + textToInsert.length() + suffix.length());
	}

	public void underlineEverything(boolean b) {
		underlineEverything = b;
		if (underlineEverything) {
			final StyleRange styleRange = new StyleRange();
			styleRange.start = 0;
			styleRange.length = this.getText().length();
			styleRange.fontStyle = SWT.NORMAL;
			styleRange.foreground = normalColor;
			styleRange.underlineStyle = SWT.UNDERLINE_ERROR;
			styleRange.underline = true;
			styleRange.underlineColor = wrongWordColor;
			setStyleRange(styleRange);
		} else {
			updateHighlight();
		}
	}

}
