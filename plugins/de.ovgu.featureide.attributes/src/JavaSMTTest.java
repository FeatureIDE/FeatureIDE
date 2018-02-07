import java.math.BigInteger;

import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;
import org.sosy_lab.java_smt.api.SolverException;

public class JavaSMTTest {

	public static void main(String[] args) {
		Configuration config;
		try {
			config = Configuration.fromCmdLineArguments(args);
			LogManager logger = BasicLogManager.create(config);
			ShutdownManager shutdown = ShutdownManager.create();

			SolverContext context = SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(), Solvers.SMTINTERPOL);

			FormulaManager fmgr = context.getFormulaManager();

			BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
			IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();

			IntegerFormula a = imgr.makeVariable("a"), b = imgr.makeVariable("b"), c = imgr.makeVariable("c");
			BooleanFormula constraint =
				bmgr.and(bmgr.or(imgr.equal(imgr.add(a, b), c), imgr.equal(imgr.add(a, c), imgr.multiply(imgr.makeNumber(2), b))), imgr.greaterThan(a, b));

			System.out.println(constraint.toString());

			try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
				prover.addConstraint(constraint);
				boolean isUnsat = prover.isUnsat();
				if (!isUnsat) {
					Model model = prover.getModel();

					BigInteger valuea = model.evaluate(a);
					BigInteger valueb = model.evaluate(b);
					BigInteger valuec = model.evaluate(c);
					System.out.println("A: " + valuea + " and B: " + valueb + " and C: " + valuec);
				}
			} catch (SolverException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		} catch (InvalidConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
