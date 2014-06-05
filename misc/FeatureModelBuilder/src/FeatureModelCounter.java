
/**
 * A minimized form of a feature model.<br>
 * It saves the hash code of the model.
 * @author Jens Meinicke
 *
 */
public class FeatureModelCounter {
	
	Double hashCode;
	
	public FeatureModelCounter(Double hashCode) {
		this.hashCode = hashCode;
	}
	
	@Override
	public boolean equals(Object obj) {
		return hashCode.equals(obj);
	}

}
