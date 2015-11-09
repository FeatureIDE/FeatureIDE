package de.ovgu.featureide.ui.interfacegen;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

public class ParameterTest implements Iterator<ParameterTest.ParameterSet>, Iterable<ParameterTest.ParameterSet> {

	private static final String EMPTY_STRING = "";

	public static class Parameter<T> {
		private final String name;
		private final T[] range;

		public Parameter(T[] range) {
			this(EMPTY_STRING, range);
		}

		public Parameter(String name, T[] range) {
			this.name = name;
			this.range = range;
		}
	}
	
	public int[] index = null;
	
	public class Index {
		private long id = 0;
		private int[] indexValues;

		public Index() {
			this.indexValues = new int[parameterList.size()];
		}
		
		public Index inc() {
			id++;
			for (int i = 0; i < indexValues.length; i++) {
				
			}
			return this;
		}
	}
	
	
	

	public static class ParameterSet {

	}

	private final List<Parameter<?>> parameterList = new ArrayList<>();
	
	private final List<List<Object>> parameterValuesList = new ArrayList<>();
	private final List<String> parameterNames = new ArrayList<>();

	public void addParameter(List<Object> values) {
		addParameter(values, EMPTY_STRING);
	}

	public void addParameter(List<Object> values, String name) {
		parameterValuesList.add(values);
		parameterNames.add(name);
	}
	
	public void addParameter(Parameter<?> parameter) {
		parameterList.add(parameter);
	}

	public void nextParameterSet() {
		final Iterator<List<Object>> it = parameterValuesList.iterator();
		//		it.next().iterator()
	}

	@Override
	public Iterator<ParameterSet> iterator() {
		return this;
	}

	@Override
	public boolean hasNext() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public ParameterSet next() {
		// TODO Auto-generated method stub
		return null;
	}
}
