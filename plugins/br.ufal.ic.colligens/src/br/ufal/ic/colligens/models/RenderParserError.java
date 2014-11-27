package br.ufal.ic.colligens.models;

import scala.Function1;
import scala.Function3;
import scala.Tuple3;
import br.ufal.ic.colligens.util.Log;
import de.fosd.typechef.error.Position;
import de.fosd.typechef.featureexpr.FeatureExpr;

public class RenderParserError implements
		Function3<FeatureExpr, String, Position, Object> {

	private FileProxy fileProxie;

	/**
	 * @param fileProxie
	 */
	public void setFile(FileProxy fileProxie) {
		this.fileProxie = fileProxie;
	}

	@Override
	public Object apply(FeatureExpr featureExpr, String msg, Position position) {
		if (position.getFile().contains(fileProxie.getFileToAnalyse())) {
			Log log = new Log(fileProxie, position.getLine(),position.getColumn(),
					featureExpr.toString(), "", msg);
			fileProxie.getLogs().add(log);
		}
		// System.out.println("parser error " + fileProxie.getLogs().size());
		return null;
	}

	@Override
	public Function1<FeatureExpr, Function1<String, Function1<Position, Object>>> curried() {
		return null;
	}

	@Override
	public Function1<Tuple3<FeatureExpr, String, Position>, Object> tupled() {
		return null;
	}

}
