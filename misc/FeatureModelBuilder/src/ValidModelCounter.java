import java.util.LinkedList;

import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 * Counts possible feature models without dead features.
 * @author Jens Meinicke
 *
 */
public class ValidModelCounter {
	private static double POW;
	
	public static void main(String[] args) {
		count_2();
		count_3();
		count_4();
		count_5();
		for (int i = 1; i <= 4;i++) {
			System.out.println(i + " " + calculate(i));
		}
	}
	
	static long calculate(int countFeature) {
		FeatureModel model = new FeatureModel();
		model.setRoot(new Feature(model, "root"));
		model.getRoot().setAnd();
		for (int i = 0;i < Math.pow(2, countFeature);i++) {
			Feature f = new Feature(model, "C" + i);
			f.setMandatory(false);
			model.addFeature(f);
			model.getRoot().addChild(f);			
		}
		for (int i = 1; i <= countFeature;i++) {
			LinkedList<Literal>constraintFeatures = new LinkedList<Literal>();
			int j = 0;
			double pow = Math.pow(2, i);
			for (Feature child : model.getRoot().getChildren()) {
				double x = (j%pow) - pow/2;
				if (x < 0) {
					constraintFeatures.add(new Literal(child.getName()));
				}
				j++;
			}
			Node node = new Or(constraintFeatures);
			Constraint c = new Constraint(model, node);
			model.addConstraint(c);
		}
		print(model);
		System.out.println();
		return new Configuration(model, false, true).number(Integer.MAX_VALUE);
	}

	static void print(FeatureModel fm) { 
		System.out.print("(");
		boolean added = false;
		for (Feature f : fm.getRoot().getChildren()) {
			if (added) {
				System.out.print("||");
			}
			System.out.print(f);
			added = true;
		}
		System.out.print(")");
		for (Constraint c : fm.getConstraints()) {
			System.out.print( "/\\(");
			System.out.print(c);
			System.out.print(")");
		}
	}
	
//  F0 or F2 F0 or F1 
	static void count_2() {
		long counter = 0;
		for (int i = 0;i < Math.pow(2, Math.pow(2, 2));i++) {
			if ((f(0,i) || f(2,i)) && (f(0,i) || f(1,i))) {
				counter++;
			} 
		}
		System.out.println(counter);
	}
	
//	F0 or F2 or F4 or F6 F0 or F1 or F4 or F5 F0 or F1 or F2 or F3 
	static void count_3() {
		POW = Math.pow(2, Math.pow(2, 3));
		long counter = 0;
		for (int i = 0;i < POW;i++) {
			if (f(0, i) || f(1, i) || f(2,i) || f(3,i))
				if (f(0, i) || f(2, i) || f(4, i) || f(6, i))
					if (f(0, i) || f(1, i) || f(4, i) || f(5, i))
						counter++;
		}
		System.out.println(counter);
	}
	
//	F0 or F2 or F4 or F6 or F8 or F10 or F12 or F14 
//	F0 or F1 or F4 or F5 or F8 or F9 or F12 or F13 
//	F0 or F1 or F2 or F3 or F8 or F9 or F10 or F11 
//	F0 or F1 or F2 or F3 or F4 or F5 or F6 or F7 
	static void count_4() {
		POW = Math.pow(2, Math.pow(2, 4));
		double counter = 0;
		for (double i = 0;i < POW;i++) {
			if (f(0, i) || f(1, i) || f(2,i) || f(3,i) || f(4, i) || f(5, i) || f(6,i) || f(7,i))
			if (f(0, i) || f(1, i) || f(2,i) || f(3,i) || f(8, i) || f(9, i) || f(10,i) || f(11,i))
			if (f(0, i) || f(1, i) || f(4,i) || f(5,i) || f(8, i) || f(9, i) || f(12,i) || f(13,i))
			if (f(0, i) || f(2, i) || f(4,i) || f(6,i) || f(8, i) || f(10, i) || f(12,i) || f(14,i))
				counter++;
		}
		System.out.println(counter);
	}
	
//	F0 or F2 or F4 or F6 or F8 or F10 or F12 or F14 or F16 or F18 or F20 or F22 or F24 or F26 or F28 or F30 
//	F0 or F1 or F4 or F5 or F8 or F9 or F12 or F13 or F16 or F17 or F20 or F21 or F24 or F25 or F28 or F29 
//	F0 or F1 or F2 or F3 or F8 or F9 or F10 or F11 or F16 or F17 or F18 or F19 or F24 or F25 or F26 or F27 
//	F0 or F1 or F2 or F3 or F4 or F5 or F6 or F7 or F16 or F17 or F18 or F19 or F20 or F21 or F22 or F23 
//	F0 or F1 or F2 or F3 or F4 or F5 or F6 or F7 or F8 or F9 or F10 or F11 or F12 or F13 or F14 or F15 
	static volatile double counter_sum = 0;
	static void count_5() {
		POW = Math.pow(2, Math.pow(2, 5));
		LinkedList<Thread> threads = new LinkedList<Thread>();
		for (int nr = 0;nr < Runtime.getRuntime().availableProcessors(); nr++) {
			final int threadNr = nr;
			Thread t  = new Thread() {
				private double counter = 0;
				public void run() {
					for (double i = threadNr;i < POW;i+=4) {
						if (i % 1000000 == 0) {
							System.out.println(POW-i);
						}
						if (isNotDead_5(i)) {
							counter++;
						}
					}
					counter_sum += counter;
				};
			};
			threads.add(t);
			t.start();
		}
		for (Thread t : threads) {
			try {
				t.join();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		System.out.println(counter_sum);
	}
	private static boolean isNotDead_5(double i) {
			return ((f(0, i) || f(1, i) || f(2,i) || f(3,i) || f(4, i) || f(5, i) || f(6,i) || f(7,i) ||
				f(8, i) || f(9, i) || f(10,i)|| f(11,i)|| f(12, i)|| f(13, i)|| f(14,i)|| f(15,i)))
			&& ((f(0, i) || f(1, i) || f(2,i) || f(3,i) || f(4, i) || f(5, i) || f(6,i) || f(7,i) ||
				f(16, i)|| f(17, i)|| f(18,i)|| f(19,i)|| f(20, i)|| f(21, i)|| f(22,i)|| f(23,i)))
			&& ((f(0, i) || f(1, i) || f(2,i) || f(3,i) || f(8, i) || f(9, i) || f(10,i)|| f(11,i)||
				f(16, i)|| f(17, i)|| f(18,i)|| f(19,i)|| f(24, i)|| f(25, i)|| f(26,i)|| f(27,i)))
			&& ((f(0, i) || f(1, i) || f(4,i) || f(5,i) || f(8, i) || f(9, i) || f(12,i)|| f(13,i)||
				f(16, i)|| f(17, i)|| f(20,i)|| f(21,i)|| f(24, i)|| f(25, i)|| f(28,i)|| f(29,i)))
			&& ((f(0, i) || f(2, i) || f(4,i) || f(6,i) || f(8, i) || f(10, i)|| f(12,i)|| f(14,i)||
				f(16, i)|| f(18, i)|| f(20,i)|| f(22,i)|| f(24, i)|| f(26, i)|| f(28,i)|| f(30,i)));
	}

	static double[] pow = new double[32];
	static {
		for (int i = 0; i < pow.length; i++) {
			pow[i] = Math.pow(2, i);
		}
	}
	
	static boolean f(int f, double i) {
		double d = POW/pow[f];
		return i%d >= d/2;
	}
}
