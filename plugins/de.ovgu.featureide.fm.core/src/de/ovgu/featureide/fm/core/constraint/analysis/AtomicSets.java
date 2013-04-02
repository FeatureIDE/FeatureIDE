package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.ovgu.featureide.fm.core.Feature;

public class AtomicSets {

	/**
	 * The id generator which is used to generate ids for atomic sets.
	 */
	private UniqueId idGenerator;
	
	/**
	 * All atomic sets are stored in this map.
	 */
	private Map<Integer, AtomicSet> atomicSets;
	
	/**
	 * Maps each feature name to its feature id. 
	 */
	private Map<String, Integer> f2fid;
	
	/**
	 * Maps each feature id to its associated atomic set id.
	 */
	private Map<Integer, Integer> fid2As;
	
	/**
	 * Maps each feature name to its associated atomic set id.
	 */
	private Map<String, Integer> f2As;
	
	/**
	 * @param f2fid Maps each feature to a unique integer identifier. 
	 */
	public AtomicSets(Map<String, Integer> f2fid) {
		this.idGenerator = new UniqueId();
		this.atomicSets = new HashMap<Integer, AtomicSet>();
		this.f2fid = f2fid;
		this.fid2As = new HashMap<Integer, Integer>();
		this.f2As = new HashMap<String, Integer>();
	}
	
	/**
	 * Creates a new atomic set with the given initial feature.
	 * 
	 * @param feature The initial feature of the newly created atomic set.
	 * @return The unique integer identifier of the new atomic set.
	 */
	public int newSet(Feature feature) {
		AtomicSet atomicSet = new AtomicSet(idGenerator.getNext());
		atomicSet.add(feature);
		
		atomicSets.put(atomicSet.getId(), atomicSet);
		fid2As.put(f2fid.get(feature.getName()), atomicSet.getId());
		f2As.put(feature.getName(), atomicSet.getId());
		
		return atomicSet.getId();
	}
	
	/**
	 * Adds a feature to specified atomic set.
	 * 
	 * @param id The id of the atomic set.
	 * @param feature The feature to add.
	 */
	public void add(int id, Feature feature) {
		AtomicSet atomicSet = atomicSets.get(id);
		atomicSet.add(feature);
		
		fid2As.put(f2fid.get(feature.getName()), atomicSet.getId());
		f2As.put(feature.getName(), atomicSet.getId());
	}
	
	/**
	 * Takes all features of the specified atomic sets and creates a new 
	 * atomic set.  
	 * 
	 * @param toMerge The ids of the atomic sets to merge.
	 * @return The merged atomic set.
	 */
	public AtomicSet merge(Collection<Integer> toMerge) {
		
		AtomicSet growingAtomicSet = null;
		for (Integer id : toMerge) {
			AtomicSet atomicSet = atomicSets.get(id);
			if (growingAtomicSet == null) {
				growingAtomicSet = atomicSet;
			} else {
				atomicSets.remove(id);
				for (Feature feature : atomicSet.getFeatures()) {
					add(growingAtomicSet.getId(), feature);
				}
			}
		}
		
		return growingAtomicSet;
	}
	
	public int fid2As(int fid) {
		return fid2As.get(fid);
	}
	
	public int f2As(String feature) {
		return f2As.get(feature);
	}
	
	public AtomicSet getAtomicSet(int id) {
		return atomicSets.get(id);
	}
	
	public Collection<AtomicSet> getAtomicSets() {
		return atomicSets.values();
	}
	
	public Set<Integer> getAtomicSetIds() {
		return atomicSets.keySet();
	}
	
	public int size() {
		return atomicSets.size();
	}
	
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		
		for (Iterator<AtomicSet> it = atomicSets.values().iterator(); it.hasNext(); ) {
			sb.append(it.next().toString());
			if (it.hasNext())
				sb.append("\n");
		}
		
		return sb.toString();
	}
}
