package br.ufal.ic.colligens.controllers.core;

import java.util.LinkedList;
import java.util.List;
import java.util.Stack;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirectiveCommand;
import de.ovgu.featureide.core.fstmodel.preprocessor.PPModelBuilder;

/**
 * Build the FSTModel for C projects.
 *
 * @author Francisco Dalton thanks to:
 * @author Christoph Giesel
 * @author Marcus Kamieth
 * @author Sebastian Krieter
 *
 */
public class CPPModelBuilder extends PPModelBuilder {

	public static final String OPERATORS = "[\\s!=<>\",;&\\^\\|\\(\\)]";
	public static final String REGEX = "(\\s*#.*" + OPERATORS + ")(%s)(" + OPERATORS + ")";

	public static final String COMMANDS = "if|ifdef|ifndef|elif|else|define|undef|endif";

	Pattern patternCommands = Pattern.compile("\\s*#(" + COMMANDS + ")");

	public CPPModelBuilder(IFeatureProject featureProject) {
		super(featureProject);
	}

	@Override
	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		// for preprocessor outline
		final Stack<FSTDirective> directivesStack = new Stack<FSTDirective>();
		final LinkedList<FSTDirective> directivesList = new LinkedList<FSTDirective>();
		int id = 0;

		for (int i = 0; i < lines.size(); i++) {
			String line = lines.get(i);

			// if line is preprocessor directive
			if (line.matches("\\s*#")) {
				FSTDirectiveCommand command = null;

				if (line.matches("\\s*#if[ (]")) {// 1
					command = FSTDirectiveCommand.IF;
				} else if (line.matches("\\s*#ifdef[ (]")) {// 2
					command = FSTDirectiveCommand.IFDEF;
				} else if (line.matches("\\s*#ifndef[ (]")) {// 3
					command = FSTDirectiveCommand.IFNDEF;
				} else if (line.matches("\\s*#elif[ (]")) {// 4
					command = FSTDirectiveCommand.ELIF;
				} else if (line.matches("\\s*#else")) {// 7
					command = FSTDirectiveCommand.ELSE;
				} else if (line.matches("\\s*#define[ (]")) {// 9
					command = FSTDirectiveCommand.DEFINE;
				} else if (line.matches("//\\s*#undef[ (]")) {// 10
					command = FSTDirectiveCommand.UNDEFINE;
				} else if (!line.matches("//\\s*#endif")) {// 11
					continue;
				}

				if (command == null) {
					if (!directivesStack.isEmpty()) {
						directivesStack.peek().setEndLine(i, line.length());
						while (!directivesStack.isEmpty()) {
							final FSTDirective parent = directivesStack.pop();
							if ((parent.getCommand() != FSTDirectiveCommand.ELIF) && (parent.getCommand() != FSTDirectiveCommand.ELSE)) {
								break;
							}
						}
					}
				} else {
					final FSTDirective directive = new FSTDirective();

					if (command == FSTDirectiveCommand.ELSE) {
						if (!directivesStack.isEmpty()) {
							directivesStack.peek().setEndLine(i, 0);
							directive.setFeatureNames(directivesStack.peek().getFeatureNames());
						}
					} else if (command == FSTDirectiveCommand.ELIF) {
						if (!directivesStack.isEmpty()) {
							directivesStack.peek().setEndLine(i, 0);
						}
					}

					directive.setCommand(command);

					final Matcher m = patternCommands.matcher(line);
					line = m.replaceAll("").trim(); // #ifdef => ""

					if (directive.getFeatureNames() == null) {
						directive.setFeatureNames(getFeatureNames(line));
					}
					directive.setExpression(line);
					directive.setStartLine(i, 0);
					directive.setId(id++);

					if (directivesStack.isEmpty()) {
						directivesList.add(directive);
					} else {
						directivesStack.peek().addChild(directive);
					}

					if ((command != FSTDirectiveCommand.DEFINE) && (command != FSTDirectiveCommand.UNDEFINE)) {
						directivesStack.push(directive);
					}
				}
			}
		}
		return directivesList;
	}

	@Override
	protected List<String> getFeatureNames(String expression) {
		final List<String> featureNameList = new LinkedList<String>();
		featureNameList.add(expression.replaceAll("[()]|defined", "").trim());
		return featureNameList;
	}

	@Override
	protected boolean containsFeature(String text, String feature) {
		return contains(text, feature);
	}

	/**
	 * the Pattern: <ul> <li>set flag DOTALL</li> <li>match any characters</li> <li>match any whitespace characters</li> <li>match "//# if/...
	 * [operators]feature[operators]"</li> <li>match any further characters</li> </ul>
	 */
	public static boolean contains(String text, String feature) {
		final Pattern pattern = Pattern.compile(String.format(REGEX, feature));
		final Matcher matcher = pattern.matcher(text);
		return matcher.find();
	}
}
