package FM;

/**
 * Variability encoding of the feature model for KeY.
 * Auto-generated class.
 */
public class FeatureModel {

	public static boolean transactionlog;
	public static boolean logging;
	public static boolean bankaccount;
	public static boolean interestestimation;
	public static boolean interest;
	public static boolean transaction;
	public static boolean creditworthiness;
	public static boolean dailylimit;
	public static boolean lock;
	public static boolean overdraft;

	/**
	 * This formula represents the validity of the current feature selection.
	 */
	public /*@pure@*/ static boolean valid() {
		return bankaccount  &&  (! (dailylimit  ||  interest  ||  overdraft  ||  creditworthiness  ||  lock  ||  logging)  ||  bankaccount)  &&  (! interestestimation  ||  interest)  &&  (! transaction  ||  lock)  &&  (! transactionlog  ||  logging)  &&  (logging  &&  transaction  ==  transactionlog);
	}

}