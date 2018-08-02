package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.IInternalVariables;
import de.ovgu.featureide.fm.core.analysis.cnf.IVariables;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Nodes;

public class ExpressionConverter {

	private static void addList(final Set<ClauseList> newExpressions, ClauseList list) {
		if (!list.isEmpty()) {
			Collections.sort(list);
			newExpressions.add(list);
		}
	}

	public static LiteralSet[] convertToArray(final List<LiteralSet> expressions) {
		return expressions.toArray(new LiteralSet[0]);
	}

	public static LiteralSet[][] convertToArray2(final List<ClauseList> expressions) {
		final List<LiteralSet[]> expressionArrays = new ArrayList<>();
		for (final ClauseList expression : expressions) {
			expressionArrays.add(expression.toArray(new LiteralSet[0]));
		}
		return expressionArrays.toArray(new LiteralSet[0][]);
	}

	public static ClauseList convert(CNF cnf) {
		final IInternalVariables variables = cnf.getInternalVariables();
		final ClauseList list = new ClauseList(variables.size());

		for (int i = 0; i < variables.size(); i++) {
			final int org = variables.convertToOriginal(i + 1);
			list.add(new LiteralSet(org));
			list.add(new LiteralSet(-org));
		}

		return list;
	}

	public static List<List<ClauseList>> convert2(CNF cnf) {
		final IInternalVariables variables = cnf.getInternalVariables();
		final List<ClauseList> list = new ArrayList<>(variables.size());

		for (int i = 0; i < variables.size(); i++) {
			final int org = variables.convertToOriginal(i + 1);
			list.add(new ClauseList(Arrays.asList(new LiteralSet(org))));
			list.add(new ClauseList(Arrays.asList(new LiteralSet(-org))));
		}

		return new ArrayList<>(Arrays.asList(list));
	}

	public static List<ClauseList> convert(CNF cnf, List<Node> expressions) {
		final Set<ClauseList> newExpressions = new HashSet<>();
		final IVariables variables = cnf.getVariables();
		for (final Node expression : expressions) {
			convert(newExpressions, variables, expression);
		}
		return new ArrayList<>(newExpressions);
	}

	public static void convert(final Set<ClauseList> newExpressions, final IVariables variables, final Node expression) {
		final ClauseList clauseList = Nodes.convert(variables, expression);
		if (!clauseList.isEmpty()) {
			for (final LiteralSet literalSet : clauseList) {
				if (literalSet.isEmpty()) {
					return;
				}
			}
			addList(newExpressions, clauseList.convert());
			addList(newExpressions, clauseList.negate());
		}
	}

}
