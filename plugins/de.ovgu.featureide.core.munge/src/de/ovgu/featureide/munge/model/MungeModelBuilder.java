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
package de.ovgu.featureide.munge.model;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Vector;
import java.util.regex.Matcher;

import org.prop4j.Node;
import org.prop4j.NodeReader;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirectiveCommand;
import de.ovgu.featureide.core.fstmodel.preprocessor.PPModelBuilder;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.base.AFeatureData;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.core.signature.base.PreprocessorFeatureData;
import de.ovgu.featureide.fm.core.filter.base.IFilter;
import de.ovgu.featureide.fm.core.functional.Functional;
import de.ovgu.featureide.munge.MungePreprocessor;
import de.ovgu.featureide.munge.signatures.MungeSignatureBuilder;

/**
 * Build the FSTModel for munge projects.
 *
 * @author Jens Meinicke
 * @author Sebastian Krieter
 * @author Marcus Pinnecke (Feature Interface)
 */
public class MungeModelBuilder extends PPModelBuilder {

	private static final class SignatureComparator implements Comparator<AbstractSignature> {

		@Override
		public int compare(AbstractSignature arg0, AbstractSignature arg1) {
			return arg0.getFirstFeatureData().getStartLineNumber() - arg1.getFirstFeatureData().getStartLineNumber();
		}
	}

	private ProjectSignatures signatures; // = MungeSignatureBuilder.build(featureProject);
	private MungePreprocessor mungePreprocessor;

	public MungeModelBuilder(IFeatureProject featureProject) {
		super(featureProject);
		refreshSignature(featureProject);
	}

	private void refreshSignature(IFeatureProject featureProject) {

		final IComposerExtensionClass composer = featureProject.getComposer();

		if (MungePreprocessor.COMPOSER_ID.equals(composer.getId())) {
			mungePreprocessor = (MungePreprocessor) composer;
			if ((mungePreprocessor != null) && mungePreprocessor.getCreateSignature()) {
				signatures = MungeSignatureBuilder.build(featureProject);
				signatures.sort(new SignatureComparator());
				model.setProjectSignatures(signatures);
				model.setExtendedFst(modelOutline);
			} else {
				model.setExtendedFst(null);
			}
		}
	}

	@Override
	protected boolean containsFeature(String text, String feature) {
		return text.contains("end[" + feature + "]");
	}

	private int curSignatureIndex = 0;

	private void updateSignatures(Deque<FSTDirective> directivesStack, int endline, SignatureIterator sigIt, ArrayList<Integer> sigLineNumber) {
		final StringBuilder sb = new StringBuilder();
		int startLine = 0;
		for (final Iterator<FSTDirective> it = directivesStack.descendingIterator(); it.hasNext();) {
			final FSTDirective fstDirective = it.next();
			switch (fstDirective.getCommand()) {
			case IF_NOT:
			case ELSE:
				sb.append("not ");
			case IF:
			case ELSE_NOT:
				sb.append('(');
				sb.append(fstDirective.getExpression());
				sb.append(')');
				break;
			default:
				return;
			}
			if (it.hasNext()) {
				sb.append(" and ");
			} else {
				startLine = fstDirective.getStartLine();
			}
		}
		if (sb.length() > 0) {
			final Node constraint = new NodeReader().stringToNode(sb.toString(), Functional.toList(featureNames));
			for (; curSignatureIndex < sigLineNumber.size(); curSignatureIndex++) {
				if (sigLineNumber.get(curSignatureIndex) >= startLine) {
					if (sigLineNumber.get(curSignatureIndex) <= endline) {
						((PreprocessorFeatureData) sigIt.next().getFirstFeatureData()).setConstraint(constraint);
					} else {
						break;
					}
				} else {
					sigIt.next();
				}
			}
		}
	}

	@Override
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		// for preprocessor outline
		final Deque<FSTDirective> directivesStack = new LinkedList<FSTDirective>();
		final LinkedList<FSTDirective> directivesList = new LinkedList<FSTDirective>();

		boolean commentSection = false;

		final String fileName;
		final String tempFileName = model.getAbsoluteClassName(currentFile);
		final int extIndex = tempFileName.lastIndexOf('.');
		if (extIndex > 0) {
			fileName = tempFileName.substring(0, extIndex);
		} else {
			fileName = tempFileName;
		}

		refreshSignature(featureProject);
		SignatureIterator sigIt = null;
		ArrayList<Integer> sigLineNumber = null;
		if ((mungePreprocessor != null) && mungePreprocessor.getCreateSignature()) {
			if (signatures == null) {
				signatures = MungeSignatureBuilder.build(featureProject);
				signatures.sort(new SignatureComparator());
				model.setProjectSignatures(signatures);
			}
			sigIt = signatures.iterator();
			sigIt.addFilter(new IFilter<AbstractSignature>() {

				@Override
				public boolean isValid(AbstractSignature object) {
					String sigName = object.getFullName();
					if (sigName.startsWith(".")) {
						sigName = sigName.substring(1);
					}
					return sigName.replace('.', '/').startsWith(fileName);
				}

			});
			sigLineNumber = new ArrayList<>();
			for (; sigIt.hasNext();) {
				sigLineNumber.add(sigIt.next().getFirstFeatureData().getStartLineNumber());
			}
			sigIt.reset();
		}

		curSignatureIndex = 0;
		final Iterator<String> linesIt = lines.iterator();

		int lineCount = 0, id = 0;

		while (linesIt.hasNext()) {
			final String line = linesIt.next();

			// if line is preprocessor directive
			if (line.contains(MungePreprocessor.COMMENT_START) || line.contains(MungePreprocessor.COMMENT_END) || commentSection) {
				final Matcher m = MungePreprocessor.OP_COM_PATTERN.matcher(line);

				while (m.find()) {
					final String completeElement = m.group(0);
					final String singleElement = m.group(2);
					final String expression = m.group(4);

					if (singleElement == null) {
						if (completeElement.equals(MungePreprocessor.COMMENT_START)) {
							commentSection = true;
						} else if (completeElement.equals(MungePreprocessor.COMMENT_END)) {
							commentSection = false;
						}
					} else {
						final FSTDirective directive = new FSTDirective();
						FSTDirectiveCommand command = null;

						if (singleElement.equals("if")) {
							command = FSTDirectiveCommand.IF;

						} else if (singleElement.equals("if_not")) {
							command = FSTDirectiveCommand.IF_NOT;
						} else if (singleElement.equals("else")) {
							command = (directivesStack.peek().getCommand() == FSTDirectiveCommand.IF) ? FSTDirectiveCommand.ELSE : FSTDirectiveCommand.ELSE_NOT;
							if ((mungePreprocessor != null) && mungePreprocessor.getCreateSignature()) {
								updateSignatures(directivesStack, lineCount, sigIt, sigLineNumber);
							}
							directivesStack.pop();
						} else if (singleElement.equals("end")) {
							if ((mungePreprocessor != null) && mungePreprocessor.getCreateSignature()) {
								updateSignatures(directivesStack, lineCount, sigIt, sigLineNumber);
							}
							directivesStack.pop().setEndLine(lineCount, m.end(0) + MungePreprocessor.COMMENT_END.length());
							continue;
						} else {
							continue;
						}

						directive.setCommand(command);
						if (expression != null) {
							directive.setExpression(expression);
							directive.setFeatureNames(getFeatureNames(expression));
						} else {
							directive.setExpression("");
							directive.setFeatureName("");
						}

						directive.setStartLine(lineCount, m.start(0) - MungePreprocessor.COMMENT_START.length());
						directive.setId(id++);

						if (!directivesStack.isEmpty()) {
							final FSTDirective top = directivesStack.peek();
							top.addChild(directive);
						} else {
							directivesList.add(directive);
						}

						directivesStack.push(directive);
					}
				}
			}
			lineCount++;
		}
		if ((mungePreprocessor != null) && mungePreprocessor.getCreateSignature()) {
			sigIt.reset();
			updateDirectives(directivesList, sigIt);
		}
		return directivesList;
	}

	private void updateDirectives(LinkedList<FSTDirective> directivesList, SignatureIterator sigIt) {
		for (final FSTDirective fstDirective : directivesList) {
			updateDirectives(fstDirective.getChildrenList(), sigIt);
			sigIt.reset();
		}
		for (final FSTDirective fstDirective : directivesList) {
			int startLine = fstDirective.getStartLine();
			startLine++;
			int endLine = fstDirective.getEndLine();
			endLine++;
			while (sigIt.hasNext()) {
				final AbstractSignature next = sigIt.next();
				final AFeatureData[] featureData = next.getFeatureData();
				final int startLineSig = featureData[0].getStartLineNumber();
				final int endLineSig = featureData[0].getEndLineNumber();
				if ((startLineSig < startLine) && (endLineSig > endLine)) {
					fstDirective.addSig_insideOf(next);
				}

				if ((startLineSig >= startLine) && (endLineSig <= endLine)) {
					// if a children has the method already included, do nothing
					final FSTDirective[] children = fstDirective.getChildren();
					boolean alreadIncluded = false;
					for (final FSTDirective fstDirective2 : children) {
						if ((fstDirective2.getIncludedSig() != null) && fstDirective2.getIncludedSig().contains(next)) {
							alreadIncluded = true;
							break;
						}
					}
					if (!alreadIncluded) {
						fstDirective.addSig_included(next);
					}
				}
			}
			sigIt.reset();
		}
	}
}
