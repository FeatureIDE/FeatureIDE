package br.ufal.ic.colligens.util.metrics;

public class Metrics {
	private String Name;
	private String value;

	public Metrics(String name, String value) {
		super();
		Name = name;
		this.value = value;
	}

	public String getName() {
		return Name;
	}

	public String getValue() {
		return value;
	}

}
