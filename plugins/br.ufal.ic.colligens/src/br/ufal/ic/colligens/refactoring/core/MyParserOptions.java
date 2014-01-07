package br.ufal.ic.colligens.refactoring.core;

import scala.Function3;
import br.ufal.ic.colligens.models.RenderParserError;
import de.fosd.typechef.featureexpr.FeatureExpr;
import de.fosd.typechef.parser.Position;
import de.fosd.typechef.parser.c.ParserOptions;

public class MyParserOptions implements ParserOptions {
	private final RenderParserError renderParser;

	public MyParserOptions() {
		this.renderParser = new RenderParserError();
	}

	@Override
	public boolean printParserStatistics() {
		return false;
	}

	@Override
	public boolean printParserResult() {
		return true;
	}

	@Override
	public Function3<FeatureExpr, String, Position, Object> renderParserError() {
		// TODO Auto-generated method stub
		return renderParser;
	}

}
