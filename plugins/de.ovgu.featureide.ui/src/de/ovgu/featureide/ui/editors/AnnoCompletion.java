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
package de.ovgu.featureide.ui.editors;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.CompletionProposal;
import org.eclipse.jdt.internal.ui.text.java.LazyJavaCompletionProposal;
import org.eclipse.jdt.ui.text.java.ContentAssistInvocationContext;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposalComputer;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.PlatformUI;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.ui.utils.AntennaEnum;
import de.ovgu.featureide.fm.ui.utils.MungeEnum;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Syntax completion for preprocessors
 *
 * @author Reimar Schr�ter
 * @author Marcus Pinnecke
 * @author Mohammed Khaled
 * @author Iris-Maria Banciu
 */
@SuppressWarnings("restriction")
public class AnnoCompletion implements IJavaCompletionProposalComputer {

	private static final Image FEATURE_ICON = UIPlugin.getImage("FeatureIconSmall.ico");

	private JavaPreprocessor currentPreprocessor = JavaPreprocessor.Unknown;
	private Status status = Status.ShowNothing;

	List<CompletionProposal> directivesCompletionProposalList = Collections.emptyList();

	private IFile file;
	private IFeatureProject featureProject;
	private ArrayList<ICompletionProposal> finalProposalsList = new ArrayList<ICompletionProposal>();
	private CharSequence prefix;

	private final List<String> allAntennaDirectives = AntennaEnum.getAllDirectives();

	private final List<String> allMungeDirectives = MungeEnum.getAllDirectives();

	public AnnoCompletion() {

	}

	private void init() {
		file = ((IFileEditorInput) PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor().getEditorInput()).getFile();
		featureProject = CorePlugin.getFeatureProject(file);
		status = Status.ShowNothing;
		prefix = "";
	}

	@Override
	public List<IContextInformation> computeContextInformation(ContentAssistInvocationContext arg0, IProgressMonitor arg1) {
		return Collections.emptyList();
	}

	@Override
	public String getErrorMessage() {
		return null;
	}

	@Override
	public void sessionEnded() {}

	@Override
	public void sessionStarted() {
		init();
	}

	@Override
	public List<ICompletionProposal> computeCompletionProposals(ContentAssistInvocationContext arg0, IProgressMonitor arg1) {

		currentPreprocessor = JavaPreprocessor.getPreprocessor(featureProject);

		final JavaContentAssistInvocationContext context = setCurrentContext(arg0);

		if ((context == null) || (file == null) || (featureProject == null)) {
			return Collections.emptyList();
		}

		computePrefix(context);

		final Status status = computeList(context);

		if (status == Status.ShowNothing) {
			return Collections.emptyList();
		}

		setDirectivesAccordingToPreprocessor();
		finalProposalsList = new ArrayList<ICompletionProposal>();

		if (status == Status.ShowFeatures) {
			buildListOfFeatures(context);

		} else if (status == Status.ShowDirectives) {
			buildListOfDirectives(context);
		}

		return finalProposalsList;
	}

	/**
	 * @param context
	 * @param prefix
	 */
	private void buildListOfDirectives(final JavaContentAssistInvocationContext context) {
		if (currentPreprocessor == JavaPreprocessor.Munge) {
			directivesCompletionProposalList = getDirectivesWithSuggestedFeatureName(context, directivesCompletionProposalList);
		}

		for (final CompletionProposal proposal : directivesCompletionProposalList) {
			final LazyJavaCompletionProposal syntax = createLazyJavaCompletionProposal(context, proposal);

			spawnCursorInbetweenSyntaxForMunge(syntax);
			finalProposalsList.add(syntax);

		}
	}

	/**
	 * @param context
	 * @param prefix
	 */
	private void buildListOfFeatures(final JavaContentAssistInvocationContext context) {
		final List<CompletionProposal> featureCompletionProposalList = getFeatureList(featureProject);

		for (final CompletionProposal proposal : featureCompletionProposalList) {

			final LazyJavaCompletionProposal feature = createLazyJavaCompletionProposal(context, proposal);

			feature.setImage(FEATURE_ICON);

			// setCursorPostionForMunge(proposal, feature);
			finalProposalsList.add(feature);

		}
	}

	private List<CompletionProposal> getFeatureList(final IFeatureProject featureProject) {
		final Iterable<String> featureNames = FeatureUtils.getConcreteFeatureNames(featureProject.getFeatureModel());

		final LinkedList<CompletionProposal> completionProposalsList = createListOfCompletionProposals(featureNames);
		return completionProposalsList;
	}

	private LinkedList<CompletionProposal> createListOfCompletionProposals(final Iterable<String> list) {
		final LinkedList<CompletionProposal> completionProposalList = new LinkedList<CompletionProposal>();
		for (String string : list) {
			CompletionProposal proposal = null;
			proposal = CompletionProposal.create(CompletionProposal.LABEL_REF, prefix.length());
			proposal.setName((string).toCharArray());
			if (currentPreprocessor == JavaPreprocessor.Antenna) {
				string += " ";
			}
			proposal.setCompletion((string).toCharArray());

			if (string.startsWith(prefix.toString())) {
				completionProposalList.add(proposal);
			}
		}
		return completionProposalList;
	}

	private JavaContentAssistInvocationContext setCurrentContext(ContentAssistInvocationContext arg0) {
		JavaContentAssistInvocationContext context = null;
		if (arg0 instanceof JavaContentAssistInvocationContext) {
			context = (JavaContentAssistInvocationContext) arg0;
		}

		return context;
	}

	private String getFeatureNameFromCondition(String conditionLine) {
		final String featurename = conditionLine.trim().substring(conditionLine.trim().indexOf('[') + 1, conditionLine.trim().indexOf(']'));

		return featurename;
	}

	private List<CompletionProposal> getDirectivesWithSuggestedFeatureName(JavaContentAssistInvocationContext context,
			List<CompletionProposal> directivesCompletionProposalList) {
		final List<CompletionProposal> newdirectivesCompletionProposalList = directivesCompletionProposalList;
		String suggestedFeatureName = null;
		try {
			suggestedFeatureName = getSuggestedFeatureName(context);
		} catch (final BadLocationException e) {
			suggestedFeatureName = null;
		}
		if (suggestedFeatureName != null) {
			if (showJustEnd) {
				final LinkedList<CompletionProposal> completionProposalList =
					createListOfCompletionProposals(MungeEnum.getEndDirctivesWithFeatureName(suggestedFeatureName));
				newdirectivesCompletionProposalList.addAll(completionProposalList);
			} else {
				final LinkedList<CompletionProposal> completionProposalList =
					createListOfCompletionProposals(MungeEnum.getEndundElseDirctivesWithFeatureName(suggestedFeatureName));
				newdirectivesCompletionProposalList.addAll(completionProposalList);
			}

		}
		return newdirectivesCompletionProposalList;
	}

	private List<String> getAllWordsInLine(String lineContent) {
		final String[] words = lineContent.split("\\s+");
		final List<String> list = Arrays.asList(words);
		Collections.reverse(list);
		return list;
	}

	boolean showJustEnd = false;

	private String getSuggestedFeatureName(JavaContentAssistInvocationContext context) throws BadLocationException {

		int counter = 0;
		showJustEnd = false;
		final int line = context.getDocument().getLineOfOffset(context.getInvocationOffset());
		final int lineIndex = line;
		for (int i = lineIndex; i >= 0; i--) {
			final int offsetOfLine = context.getDocument().getLineOffset(i);
			final int lineLength = context.getDocument().getLineLength(i);
			final String lineContent = context.getDocument().get(offsetOfLine, lineLength);
			for (final String keyWord : getAllWordsInLine(lineContent)) {
				if (keyWord.contains("/*end[")) {
					counter++;
				}
				if (keyWord.contains("/*else[") && (counter < 1)) {
					showJustEnd = true;
				}
				if (keyWord.contains("/*if[") || keyWord.contains("/*if_not[")) {
					if (counter >= 1) {
						counter--;
						continue;
					}
					return getFeatureNameFromCondition(keyWord);
				}

			}

		}
		return null;

	}

	private void setDirectivesAccordingToPreprocessor() {
		switch (currentPreprocessor) {
		case Antenna:
			directivesCompletionProposalList = getAntennaCompletionProposals();
			break;
		case Munge:
			directivesCompletionProposalList = getMungeCompletionProposals();
			break;
		default:
			break;
		}
	}

	private void computePrefix(final JavaContentAssistInvocationContext context) {
		try {
			prefix = context.computeIdentifierPrefix();
		} catch (final BadLocationException e) {
			e.printStackTrace();
		}
	}

	private LazyJavaCompletionProposal createLazyJavaCompletionProposal(final JavaContentAssistInvocationContext context, final CompletionProposal proposal) {
		final LazyJavaCompletionProposal lazyJavaCompletionProposal = new LazyJavaCompletionProposal(proposal, context);

		lazyJavaCompletionProposal.setReplacementString(new String(proposal.getCompletion()).replaceFirst(prefix.toString(), ""));
		lazyJavaCompletionProposal.setReplacementOffset(context.getInvocationOffset());

		return lazyJavaCompletionProposal;
	}

	private void spawnCursorInbetweenSyntaxForMunge(final LazyJavaCompletionProposal syntax) {
		if (currentPreprocessor == JavaPreprocessor.Munge) {
			syntax.setCursorPosition((syntax.toString().length() - prefix.length()) - 3);
		}
	}

	private boolean lineContainsElements(String lineContent, List<String> list) {

		for (final String div : list) {
			if (lineContent.contains(div)) {
				return true;
			}
		}
		return false;
	}

	private String findLastKeyword(String context) {
		final String text = context.trim();
		final int indexofKeyword = text.lastIndexOf(" ");
		if (indexofKeyword < 0) {
			return text;
		}
		return text.substring(indexofKeyword).trim();
	}

	private Status computeList(JavaContentAssistInvocationContext context) {
		try {
			final int line = context.getDocument().getLineOfOffset(context.getInvocationOffset());
			final int offsetOfLine = context.getDocument().getLineOffset(line);
			final int lineLength = context.getDocument().getLineLength(line);
			final String lineContent = context.getDocument().get(offsetOfLine, lineLength);
			final String lastKeyword = findLastKeyword(context.getDocument().get().substring(offsetOfLine, context.getInvocationOffset()));

			getStatusAccordingToPreprocessor(lineContent, lastKeyword, context);
		}

		catch (final BadLocationException e1) {
			e1.printStackTrace();
		}
		return status;
	}

	private void getStatusAccordingToPreprocessor(String lineContent, String lastKeyword, final JavaContentAssistInvocationContext context) {
		switch (currentPreprocessor) {
		case Antenna:
			status = getStatusForAntenna(lineContent, lastKeyword, context);
			break;
		case Munge:
			status = getStatusForMunge(lineContent, lastKeyword, context);
			break;
		default:
			break;
		}
	}

	private Status getStatusForAntenna(String lineContent, String lastKeyword, final JavaContentAssistInvocationContext context) {
		final boolean triggerAutocomplete = lineContent.trim().substring(2).trim().contains("#");
		final boolean hasDirective = lineContainsElements(lineContent, allAntennaDirectives);
		final boolean directiveHasCondition = lineContainsElements(lineContent, Arrays.asList("#if", "#elif", "#condition"));
		final boolean hasFeature = lineContainsElements(lineContent, (List<String>) FeatureUtils.getConcreteFeatureNames(featureProject.getFeatureModel()));
		final boolean acceptsNewDirective = (lineContent.contains("&&") || lastKeyword.contains("||"));

		if (triggerAutocomplete && !hasDirective) {
			status = Status.ShowDirectives;
		} else {
			status = Status.ShowNothing;
		}
		if ((directiveHasCondition && !hasFeature) || (hasFeature && hasDirective && acceptsNewDirective)) {
			status = Status.ShowFeatures;
		}
		return status;
	}

	private Status getStatusForMunge(String lineContent, String lastKeyword, final JavaContentAssistInvocationContext context) {

		final boolean hasOpeningSyntax = lastKeyword.trim().contains("/*") && !lastKeyword.trim().contains("[");
		final boolean hasDirective = lineContainsElements(lastKeyword, MungeEnum.getAllDirectivesNames());
		final boolean showFeatures = lastKeyword.toCharArray()[lastKeyword.length() - 1] == '[';
		if ((hasOpeningSyntax && !hasDirective)) {
			status = Status.ShowDirectives;
		}
		if ((hasDirective && showFeatures)) {
			status = Status.ShowFeatures;
		}
		return status;
	}

	private List<CompletionProposal> getAntennaCompletionProposals() {
		final LinkedList<CompletionProposal> completionProposalList = createListOfCompletionProposals(allAntennaDirectives);
		return completionProposalList;
	}

	private List<CompletionProposal> getMungeCompletionProposals() {
		final LinkedList<CompletionProposal> completionProposalList = createListOfCompletionProposals(allMungeDirectives);

		return completionProposalList;
	}

	private enum Status {
		ShowFeatures, ShowDirectives, ShowNothing
	}

	private enum JavaPreprocessor {
		Antenna, Munge, Unknown;

		public static JavaPreprocessor getPreprocessor(final IFeatureProject featureProject) {
			switch (featureProject.getComposer().getName()) {
			case "Antenna":
				return JavaPreprocessor.Antenna;
			case "Munge":
				return JavaPreprocessor.Munge;
			default:
				return JavaPreprocessor.Unknown;
			}
		}
	}
}
