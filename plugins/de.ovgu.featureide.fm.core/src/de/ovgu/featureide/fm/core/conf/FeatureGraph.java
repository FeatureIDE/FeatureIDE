package de.ovgu.featureide.fm.core.conf;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;

import de.ovgu.featureide.fm.core.Feature;

public class FeatureGraph {
	public static final byte
			EDGE_NONE 	= 0b00000000,
			EDGE_11 	= 0b00000100, //0x04,
			EDGE_10 	= 0b00001000, //0x08,
			EDGE_1q 	= 0b00001100, //0x0c,
			EDGE_01 	= 0b00010000, //0x10,
			EDGE_00 	= 0b00100000, //0x20,
			EDGE_0q 	= 0b00110000; //0x30;

	public static final byte 
			MASK_1_11110011 = (byte) 0b11110011, //0xf3,
			MASK_0_11001111 = (byte) 0b11001111, //0xcf,
			MASK_1_00001100 = ~MASK_1_11110011,
			MASK_0_00110000 = ~MASK_0_11001111;

	public final String[] featureArray;

	private final byte[] adjMatrix;
	private final int size;
	private final HashMap<String, Integer> featureMap;
	
	public static boolean isEdge(byte edge, byte q) {
		switch (q) {
		case EDGE_NONE:
			return edge == 0;
		case EDGE_11:
		case EDGE_10:
		case EDGE_1q:
			return (edge & MASK_1_00001100) == q;
		case EDGE_01:
		case EDGE_00:
		case EDGE_0q:
			return (edge & MASK_0_00110000) == q;
		default:
			return false;
		}
	}

	public FeatureGraph(Collection<Feature> features) {
		size = features.size();
		featureMap = new HashMap<>(size << 1);
		featureArray = new String[size];

		int i = 0;
		for (Feature feature : features) {
			featureArray[i++] = feature.getName();
		}
		Arrays.sort(featureArray);
		for (int j = 0; j < featureArray.length; j++) {
			featureMap.put(featureArray[j], j);
		}

		adjMatrix = new byte[size * size];
	}

	public void implies(String implyFeature, String impliedFeature) {
		implies(implyFeature, impliedFeature, 0);
	}

	public void implies(String implyFeature, String impliedFeature, int negation) {
		switch (negation) {
		case 0:
			setEdge(implyFeature, impliedFeature, FeatureGraph.EDGE_11);
			setEdge(impliedFeature, implyFeature, FeatureGraph.EDGE_00);
			break;
		case 1:
			setEdge(implyFeature, impliedFeature, FeatureGraph.EDGE_10);
			setEdge(impliedFeature, implyFeature, FeatureGraph.EDGE_10);
			break;
		case 2:
			setEdge(implyFeature, impliedFeature, FeatureGraph.EDGE_01);
			setEdge(impliedFeature, implyFeature, FeatureGraph.EDGE_01);
			break;
		case 3:
			setEdge(impliedFeature, implyFeature, FeatureGraph.EDGE_11);
			setEdge(implyFeature, impliedFeature, FeatureGraph.EDGE_00);
			break;
		}
	}

	public void setEdge(String from, String to, byte edgeType) {
		setEdge(featureMap.get(from), featureMap.get(to), edgeType);
	}

	public void setEdge(int from, int to, byte edgeType) {
		final int index = (from * size) + to;

		final byte oldValue;
		synchronized (featureArray[from]) {
			oldValue = adjMatrix[index];
		}

		final int newValue;
		switch (edgeType) {
		case EDGE_NONE:
			newValue = EDGE_NONE;
			break;
		case EDGE_0q:
			switch (oldValue & MASK_0_00110000) {
			case EDGE_NONE:
				newValue = oldValue | EDGE_0q;
				break;
			default:
				newValue = oldValue;
			}
			break;
		case EDGE_00:
		case EDGE_01:
			switch (oldValue & MASK_0_00110000) {
			case EDGE_NONE:
				newValue = oldValue | edgeType;
				break;
			case EDGE_0q:
				newValue = (oldValue & MASK_0_11001111) | edgeType;
				break;
			default:
				newValue = oldValue;
				assert ((oldValue & MASK_0_00110000) == edgeType) : (oldValue & MASK_0_00110000) + " != " + edgeType;
			}
			break;
		case EDGE_1q:
			switch (oldValue & MASK_1_00001100) {
			case EDGE_NONE:
				newValue = oldValue | EDGE_1q;
				break;
			default:
				newValue = oldValue;
			}
			break;
		case EDGE_10:
		case EDGE_11:
			switch (oldValue & MASK_1_00001100) {
			case EDGE_NONE:
				newValue = oldValue | edgeType;
				break;
			case EDGE_1q:
				newValue = (oldValue & MASK_1_11110011) | edgeType;
				break;
			default:
				newValue = oldValue;
				if ((oldValue & MASK_1_00001100) != edgeType) {
					throw new RuntimeException();
				}
				assert ((oldValue & MASK_1_00001100) == edgeType) : (oldValue & MASK_1_00001100) + " != " + edgeType;
			}
			break;
		default:
			newValue = EDGE_NONE;
		}
		synchronized (featureArray[from]) {
			adjMatrix[index] = (byte) newValue;
		}
	}

	//public byte getEdge(String from, String to) {
	//	return getEdge(featureMap.get(from), featureMap.get(to));
	//}

	public byte getEdge(int fromIndex, int toIndex) {
		final int index = (fromIndex * size) + toIndex;
		//	synchronized (featureArray[fromIndex]) {
		return adjMatrix[index];
		//	}
	}

	public void clearDiagonal() {
		for (int i = 0; i < adjMatrix.length; i += (size + 1)) {
			adjMatrix[i] = EDGE_NONE;
		}
	}

	public int getFeatureIndex(String featureName) {
		final Integer index = featureMap.get(featureName);
		return index != null ? index : -1;
	}

	public int countNeighbors(String from, boolean selected, boolean subtractReal) {
		final int fromIndex = featureMap.get(from);
		final byte mask = (selected) ? MASK_1_00001100 : MASK_0_00110000;
		final byte unrealEdge = (selected) ? EDGE_1q : EDGE_0q;

		int count = 0;
		for (int i = (fromIndex * size), end = i + size; i < end; i++) {
			final int edge = (adjMatrix[i] & mask);
			count += (edge == 0 || (subtractReal && edge != unrealEdge)) ? 0 : 1;
		}

		return count;
	}

	// visited: 0 not visited, 1 visited (unknown status), 2 visited (known status)
	public void dfs(byte[] visited, int curFeature, boolean selected) {
		//	System.out.println(featureArray[curFeature] + " " + selected);
		visited[curFeature] = 2;

		for (int j = 0; j < visited.length; j++) {
			final byte visit = visited[j];
			if (visit < 2) {
				final byte childSelected;
				if (selected) {
					switch (getEdge(curFeature, j) & MASK_1_00001100) {
					case EDGE_10:
						// don't select child
						childSelected = 0;
						visited[j] = 2;
						//						System.out.println("\tq " + featureArray[j]);
						break;
					case EDGE_11:
						// select child
						childSelected = 1;
						visited[j] = 2;
						//						System.out.println("\tq " + featureArray[j]);
						break;
					case EDGE_1q:
						// ?
						if (visit == 1) {
							continue;
						}
						visited[j] = 1;
						childSelected = 2;
						//						System.out.println("\tq " + featureArray[j]);
						break;
					default:
						continue;
					}
				} else {
					switch (getEdge(curFeature, j) & MASK_0_00110000) {
					case EDGE_00:
						// don't select child
						childSelected = 0;
						visited[j] = 2;
						//						System.out.println("\t0 " + featureArray[j]);
						break;
					case EDGE_01:
						// select child
						childSelected = 1;
						visited[j] = 2;
						//						System.out.println("\t1 " + featureArray[j]);
						break;
					case EDGE_0q:
						// ?
						if (visit == 1) {
							continue;
						}
						childSelected = 2;
						visited[j] = 1;
						//						System.out.println("\tq " + featureArray[j]);
						break;
					default:
						continue;
					}
				}

				dfs_rec(visited, j, curFeature, childSelected, selected);
			}
		}
	}

	private void dfs_rec(byte[] visited, int curFeature, int parentFeature, byte selected, boolean parentSelected) {
		for (int j = 0; j < visited.length; j++) {
			final byte visit = visited[j];
			if (visit == 0) {
				final byte edge = getEdge(curFeature, j);
				switch (selected) {
				case 0:
					switch (edge & MASK_0_00110000) {
					// visit = 0, not selected, implies not selected
					case EDGE_00:
						visited[j] = 2;
						//							System.out.println("\t0 " + featureArray[j]);
						setEdge(parentFeature, j, parentSelected ? EDGE_10 : EDGE_00);
						dfs_rec(visited, j, parentFeature, (byte) 0, parentSelected);
						break;
					// visit = 0, not selected, implies selected
					case EDGE_01:
						visited[j] = 2;
						//							System.out.println("\t1 " + featureArray[j]);
						setEdge(parentFeature, j, parentSelected ? EDGE_11 : EDGE_01);
						dfs_rec(visited, j, parentFeature, (byte) 1, parentSelected);
						break;
					// visit = 0, not selected, implies ?
					case EDGE_0q:
						visited[j] = 1;
						//							System.out.println("\tq " + featureArray[j]);
						setEdge(parentFeature, j, parentSelected ? EDGE_1q : EDGE_0q);
						dfs_rec(visited, j, parentFeature, (byte) 2, parentSelected);
						break;
					// default ???
					}
					break;
				case 1:
					switch (edge & MASK_1_00001100) {
					// visit = 0, selected, implies not selected
					case EDGE_10:
						visited[j] = 2;
						//							System.out.println("\t0 " + featureArray[j]);
						setEdge(parentFeature, j, parentSelected ? EDGE_10 : EDGE_00);
						dfs_rec(visited, j, parentFeature, (byte) 0, parentSelected);
						break;
					// visit = 0, selected, implies selected
					case EDGE_11:
						visited[j] = 2;
						//							System.out.println("\t1 " + featureArray[j]);
						setEdge(parentFeature, j, parentSelected ? EDGE_11 : EDGE_01);
						dfs_rec(visited, j, parentFeature, (byte) 1, parentSelected);
						break;
					// visit = 0, selected, implies ?
					case EDGE_1q:
						visited[j] = 1;
						//							System.out.println("\tq " + featureArray[j]);
						setEdge(parentFeature, j, parentSelected ? EDGE_1q : EDGE_0q);
						dfs_rec(visited, j, parentFeature, (byte) 2, parentSelected);
						break;
					// default ???
					}
					break;
				case 2:
					if (edge > 0) {
						visited[j] = 1;
						//						System.out.println("\tq " + featureArray[j]);
						setEdge(parentFeature, j, parentSelected ? EDGE_1q : EDGE_0q);
						dfs_rec(visited, j, parentFeature, (byte) 2, parentSelected);
					}
					break;
				}
			} else if (visit == 1) {
				final byte edge = getEdge(curFeature, j);
				switch (selected) {
				case 0:
					switch (edge & MASK_0_00110000) {
					// visit = 1, not selected, implies not selected
					case EDGE_00:
						visited[j] = 2;
						//							System.out.println("\t0 " + featureArray[j]);
						setEdge(parentFeature, j, parentSelected ? EDGE_10 : EDGE_00);
						dfs_rec(visited, j, parentFeature, (byte) 0, parentSelected);
						break;
					// visit = 1, not selected, implies selected
					case EDGE_01:
						visited[j] = 2;
						//							System.out.println("\t1 " + featureArray[j]);
						setEdge(parentFeature, j, parentSelected ? EDGE_11 : EDGE_01);
						dfs_rec(visited, j, parentFeature, (byte) 1, parentSelected);
						break;
					// default ???
					}
					break;
				case 1:
					switch (edge & MASK_1_00001100) {
					// visit = 1, selected, implies not selected
					case EDGE_10:
						visited[j] = 2;
						//							System.out.println("\t0 " + featureArray[j]);
						setEdge(parentFeature, j, parentSelected ? EDGE_10 : EDGE_00);
						dfs_rec(visited, j, parentFeature, (byte) 0, parentSelected);
						break;
					// visit = 1, selected, implies selected
					case EDGE_11:
						visited[j] = 2;
						//							System.out.println("\t1 " + featureArray[j]);
						setEdge(parentFeature, j, parentSelected ? EDGE_11 : EDGE_01);
						dfs_rec(visited, j, parentFeature, (byte) 1, parentSelected);
						break;
					// default ???
					}
					break;
				}
			}
		}
	}
}
