package br.ufal.ic.colligens.models;

import br.ufal.ic.colligens.util.Log;
import scala.collection.Iterator;
import scala.collection.immutable.*;
import de.fosd.typechef.typesystem.TypeError;

@SuppressWarnings("rawtypes")
public class RenderTypeError {

	private List errors;
	private FileProxy fileProxie;

	public RenderTypeError(List errors) {
		this.errors = errors;
	}

	/**
	 * @param fileProxie
	 */
	public void setFile(FileProxy fileProxie) {
		this.fileProxie = fileProxie;
	}

	public void run() {
		if (errors == null)
			return;

		for (Iterator iterator = errors.iterator(); iterator.hasNext();) {
			TypeError error = (TypeError) iterator.next();
			Log log = new Log(fileProxie, error.where().getPositionFrom()
					.getLine(), error.condition().toString(), "", error.msg());

			fileProxie.getLogs().add(log);

		}

	}
}
