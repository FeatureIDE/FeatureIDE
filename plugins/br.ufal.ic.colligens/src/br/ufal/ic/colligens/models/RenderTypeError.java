package br.ufal.ic.colligens.models;

import static de.ovgu.featureide.fm.core.localization.StringTable.TYPE_ERROR;

import br.ufal.ic.colligens.util.Log;
import de.fosd.typechef.error.TypeChefError;
import scala.Function1;
import scala.runtime.BoxedUnit;

public class RenderTypeError implements Function1<TypeChefError, Object> {

	private FileProxy fileProxy;

	/**
	 * @param fileProxie
	 */
	public void setFile(FileProxy fileProxy) {
		this.fileProxy = fileProxy;
	}

	@Override
	public Object apply(TypeChefError typeError) {

		if (typeError.where().getPositionFrom().getFile().contains(fileProxy.getFileToAnalyse())) {
			boolean isNew = true;
			if (fileProxy.getLogs().size() > 0) {
				for (final Log log : fileProxy.getLogs()) {
					if (log.getFeature().equals(typeError.condition().toString()) && log.getMessage().equals(typeError.msg())
						&& log.getSeverity().equals(typeError.severity().toString())) {

						isNew = false;
					}
				}
			}

			if (isNew || (fileProxy.getLogs().size() == 0)) {
				final Log newlog = new Log(fileProxy, typeError.where().getPositionFrom().getLine(), typeError.where().getPositionFrom().getColumn(),
						typeError.condition().toString(), typeError.severity().toString(), typeError.msg());

				fileProxy.getLogs().add(newlog);
				System.out.println(TYPE_ERROR + fileProxy.getLogs().size());
			}

		}
		return null;

	}

	@Override
	public <A> Function1<TypeChefError, A> andThen(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcDD$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcDF$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcDI$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcDJ$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcFD$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcFF$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcFI$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcFJ$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcID$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcIF$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcII$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcIJ$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcJD$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcJF$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcJI$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcJJ$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcVD$sp(Function1<BoxedUnit, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcVF$sp(Function1<BoxedUnit, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcVI$sp(Function1<BoxedUnit, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcVJ$sp(Function1<BoxedUnit, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcZD$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcZF$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcZI$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public <A> Function1<Object, A> andThen$mcZJ$sp(Function1<Object, A> arg0) {

		return null;
	}

	@Override
	public double apply$mcDD$sp(double arg0) {

		return 0;
	}

	@Override
	public double apply$mcDF$sp(float arg0) {

		return 0;
	}

	@Override
	public double apply$mcDI$sp(int arg0) {

		return 0;
	}

	@Override
	public double apply$mcDJ$sp(long arg0) {

		return 0;
	}

	@Override
	public float apply$mcFD$sp(double arg0) {

		return 0;
	}

	@Override
	public float apply$mcFF$sp(float arg0) {

		return 0;
	}

	@Override
	public float apply$mcFI$sp(int arg0) {

		return 0;
	}

	@Override
	public float apply$mcFJ$sp(long arg0) {

		return 0;
	}

	@Override
	public int apply$mcID$sp(double arg0) {

		return 0;
	}

	@Override
	public int apply$mcIF$sp(float arg0) {

		return 0;
	}

	@Override
	public int apply$mcII$sp(int arg0) {

		return 0;
	}

	@Override
	public int apply$mcIJ$sp(long arg0) {

		return 0;
	}

	@Override
	public long apply$mcJD$sp(double arg0) {

		return 0;
	}

	@Override
	public long apply$mcJF$sp(float arg0) {

		return 0;
	}

	@Override
	public long apply$mcJI$sp(int arg0) {

		return 0;
	}

	@Override
	public long apply$mcJJ$sp(long arg0) {

		return 0;
	}

	@Override
	public void apply$mcVD$sp(double arg0) {

	}

	@Override
	public void apply$mcVF$sp(float arg0) {

	}

	@Override
	public void apply$mcVI$sp(int arg0) {

	}

	@Override
	public void apply$mcVJ$sp(long arg0) {

	}

	@Override
	public boolean apply$mcZD$sp(double arg0) {

		return false;
	}

	@Override
	public boolean apply$mcZF$sp(float arg0) {

		return false;
	}

	@Override
	public boolean apply$mcZI$sp(int arg0) {

		return false;
	}

	@Override
	public boolean apply$mcZJ$sp(long arg0) {

		return false;
	}

	@Override
	public <A> Function1<A, Object> compose(Function1<A, TypeChefError> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcDD$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcDF$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcDI$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcDJ$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcFD$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcFF$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcFI$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcFJ$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcID$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcIF$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcII$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcIJ$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcJD$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcJF$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcJI$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcJJ$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, BoxedUnit> compose$mcVD$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, BoxedUnit> compose$mcVF$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, BoxedUnit> compose$mcVI$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, BoxedUnit> compose$mcVJ$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcZD$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcZF$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcZI$sp(Function1<A, Object> arg0) {

		return null;
	}

	@Override
	public <A> Function1<A, Object> compose$mcZJ$sp(Function1<A, Object> arg0) {

		return null;
	}
}
