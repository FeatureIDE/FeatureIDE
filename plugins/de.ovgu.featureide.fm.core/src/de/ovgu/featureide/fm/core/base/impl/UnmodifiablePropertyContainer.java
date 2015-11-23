package de.ovgu.featureide.fm.core.base.impl;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.ovgu.featureide.fm.core.base.IPropertyContainer;

public class UnmodifiablePropertyContainer implements IPropertyContainer {

	private IPropertyContainer container;
	
	static UnsupportedOperationException exception = new UnsupportedOperationException("Manipulation is not allowed. This is an unmodifiable property container");

	public UnmodifiablePropertyContainer(IPropertyContainer container) {
		this.container = container;
	}

	@Override
	public <T> T get(String key, T defaultValue) {
		return container.get(key, defaultValue);
	}

	@Override
	public Type getDataType(String key) throws NoSuchPropertyException {
		return container.getDataType(key);
	}

	@Override
	public <T> T get(String key) throws NoSuchPropertyException {
		return container.get(key);
	}

	@Override
	public boolean has(String key) {
		return container.has(key);
	}

	@Override
	public Set<String> keySet() {
		final Set<String> set = new HashSet<>();
		for (final String s : container.keySet()) {
			set.add(new String(s));
		}
		return set;
	}

	@Override
	public Set<Entry<String, Type, Object>> entrySet() {
		return Collections.unmodifiableSet(container.entrySet());
	}

	@Override
	public void setEntrySet(Set<Entry<String, Type, Object>> entries) {
		throw exception;
	}

	@Override
	public void remove(String key) throws NoSuchPropertyException {
		throw exception;
	}

	@Override
	public <T> void set(String key, Type type, T value) {
		throw exception;
	}

}
