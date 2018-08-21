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
import java.util.List;
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
import org.prop4j.ErrorType;
import org.prop4j.ErrorType.ErrorEnum;

import de.ovgu.featureide.fm.core.Operator;

/**
 * Simple syntax highlighted editor
 *
 * @author Marcus Pinnecke
 */
public class SimpleSyntaxHighlightEditor extends StyledText {

	private final StyleRange defaultStyleRange = new StyleRange();
	private static final Pattern nonOperators = Pattern.compile("\"[^\"]*\"");

	/**
	 * @param parent
	 * @param style
	 */
	public SimpleSyntaxHighlightEditor(Composite parent, int style, final String[] keywords) {
		super(parent, style);

		keywordColor = Display.getDefault().getSystemColor(SWT.COLOR_DARK_RED);
		wrongWordColor = Display.getDefault().getSystemColor(SWT.COLOR_RED);
		normalColor = Display.getDefault().getSystemColor(SWT.COLOR_BLACK);
		setFont(JFaceResources.getTextFont());

		super.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {

				updateHighlight(new ErrorType(ErrorEnum.None));
			}
		});
	}

	private final Color keywordColor;
	private final Color wrongWordColor;
	private final Color normalColor;
	private boolean keywordsUnderline;
	private int index;

	/**
	 * Updates highlight according to error type.
	 *
	 * @param errorType
	 * @author Mohammed Khaled
	 * @author Iris-Maria Banciu
	 */
	public void updateHighlight(ErrorType errorType) {
		final String text = super.getText();
		keywordsUnderline = false;
		defaultStyleRange();

		switch (errorType.getError()) {
		case Default:
			defaultStyleRange();
			highlightEverything();
			break;
		case InvalidExpressionLeft:
			defaultStyleRange();
			hightlightBetween(errorType);
			break;
		case InvalidExpressionRight:
			defaultStyleRange();
			hightlightBetween(errorType);
			break;
		case InvalidFeatureName:
			defaultStyleRange();
			underlineKeyword(errorType.getKeyword());
			break;
		default:
			break;
		}
		hightlightKeywords(text);
	}

	private void defaultStyleRange() {
		defaultStyleRange.start = 0;
		defaultStyleRange.length = super.getText().length();
		defaultStyleRange.fontStyle = SWT.NORMAL;
		defaultStyleRange.underline = false;
		defaultStyleRange.foreground = normalColor;
		setStyleRange(defaultStyleRange);
	}

	private void highlightEverything() {
		setUnderlineForError(defaultStyleRange);
		setStyleRange(defaultStyleRange);
	}

	private void underlineKeyword(String keyword) {
		final Matcher operatorMatcher = Pattern.compile(keyword).matcher(super.getText());
		final Matcher nonOperatorMatcher = nonOperators.matcher(super.getText());
		final List<Match> keywordPositions = extractRegexMatchesFromText(nonOperatorMatcher, operatorMatcher);
		for (final Match match : keywordPositions) {
			final StyleRange highlightKeywordStyleRange = (StyleRange) defaultStyleRange.clone();
			highlightKeywordStyleRange.start = match.start;
			highlightKeywordStyleRange.length = match.end - match.start;
			setUnderlineForError(highlightKeywordStyleRange);
			setStyleRange(highlightKeywordStyleRange);

		}

	}

	private void hightlightBetween(ErrorType errorType) {
		int start = 0;
		int end = super.getText().length();
		if (errorType.getError() == ErrorEnum.InvalidExpressionRight) {
			keywordsUnderline = true;
			index = end - errorType.getEndErrorIndex();
			start = errorType.getEndErrorIndex() - 2;
			end = super.getText().length();
		} else if (errorType.getError() == ErrorEnum.InvalidExpressionLeft) {
			keywordsUnderline = true;
			index = end - errorType.getEndErrorIndex();
			start = 0;
			end = (end - errorType.getEndErrorIndex()) + 1;
		}

		final StyleRange hightlightBetweenStyleRange = new StyleRange();
		hightlightBetweenStyleRange.start = start;
		hightlightBetweenStyleRange.length = end - start;
		setUnderlineForError(hightlightBetweenStyleRange);
		setStyleRange(hightlightBetweenStyleRange);

	}

	private void setUnderlineForError(final StyleRange hightlightBetweenStyleRange) {
		hightlightBetweenStyleRange.underlineStyle = SWT.UNDERLINE_ERROR;
		hightlightBetweenStyleRange.underline = true;
		hightlightBetweenStyleRange.underlineColor = wrongWordColor;
	}

	private static class Match {

		private final int start, end;

		public Match(int start, int end) {
			this.start = start;
			this.end = end;
		}
	}

	private void hightlightKeywords(String text) {

		final Matcher operatorMatcher = Pattern.compile(Operator.REGEX).matcher(text);
		final Matcher nonOperatorMatcher = nonOperators.matcher(text);

		final List<Match> keywordPositions = extractRegexMatchesFromText(nonOperatorMatcher, operatorMatcher);

		// highlight keywords in text
		for (final Match match : keywordPositions) {
			final StyleRange keywordsStyleRange = (StyleRange) defaultStyleRange.clone();

			keywordsStyleRange.start = match.start;
			keywordsStyleRange.length = match.end - match.start;
			keywordsStyleRange.fontStyle = SWT.BOLD;
			keywordsStyleRange.foreground = keywordColor;

			underlineWrongKeywords(match, keywordsStyleRange);

			setStyleRange(keywordsStyleRange);
		}
	}

	private void underlineWrongKeywords(final Match match, final StyleRange keywordsStyleRange) {
		if ((keywordsUnderline && (match.end <= index))) {
			setUnderlineForError(keywordsStyleRange);
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

	private List<Match> extractRegexMatchesFromText(final Matcher matchAnything, final Matcher regexMatcher) {
		final List<Match> keywordPositions = new ArrayList<>();
		Match nonOperatorMatch = null;
		if (matchAnything.find()) {
			nonOperatorMatch = new Match(matchAnything.start(), matchAnything.end());
		}
		while (regexMatcher.find()) {
			final int start = regexMatcher.start();
			final int end = regexMatcher.end();

			while ((nonOperatorMatch != null) && (start > nonOperatorMatch.end)) {
				if (matchAnything.find()) {
					nonOperatorMatch = new Match(matchAnything.start(), matchAnything.end());
				} else {
					nonOperatorMatch = null;
				}
			}
			if ((nonOperatorMatch == null) || !((start < nonOperatorMatch.end) && (end > nonOperatorMatch.start))) {
				keywordPositions.add(new Match(start, end));
			}
		}
		return keywordPositions;
	}
}
