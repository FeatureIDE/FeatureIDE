/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.core.conf.worker;

import java.util.Arrays;

import de.ovgu.featureide.fm.core.conf.AFeatureGraph;
import de.ovgu.featureide.fm.core.conf.MatrixFeatureGraph;
import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

public class DFSThread extends AWorkerThread<String> {

	private static class SharedObjects {
		private final MatrixFeatureGraph featureGraph;
		private final boolean[] complete;

		public SharedObjects(MatrixFeatureGraph featureGraph) {
			this.featureGraph = featureGraph;
			this.complete = new boolean[featureGraph.getFeatureArray().length];
		}
	}

	private final byte[] visited;
	private final SharedObjects sharedObjects;

	public DFSThread(MatrixFeatureGraph featureGraph, WorkMonitor workMonitor) {
		super(workMonitor);
		sharedObjects = new SharedObjects(featureGraph);
		visited = new byte[featureGraph.getFeatureArray().length];
	}

	private DFSThread(DFSThread oldThread) {
		super(oldThread);
		this.sharedObjects = oldThread.sharedObjects;
		visited = new byte[oldThread.sharedObjects.featureGraph.getFeatureArray().length];
	}

	@Override
	protected void work(String object) {
		final int featureIndex = sharedObjects.featureGraph.getFeatureIndex(object);
		Arrays.fill(visited, (byte) 0);
		dfs(visited, sharedObjects.complete, featureIndex, true);
		Arrays.fill(visited, (byte) 0);
		dfs(visited, sharedObjects.complete, featureIndex, false);
		sharedObjects.complete[featureIndex] = true;
	}

	@Override
	protected DFSThread newThread() {
		return new DFSThread(this);
	}

	// visited: 0 not visited, 1 visited (unknown status), 2 visited (known status)
	private void dfs(byte[] visited, boolean[] complete, int curFeature, boolean selected) {
		//	System.out.println(featureArray[curFeature] + " " + selected);
		visited[curFeature] = 2;

		for (int j = 0; j < visited.length; j++) {
			final byte visit = visited[j];
			if (visit < 2) {
				final byte childSelected;
				if (selected) {
					switch (sharedObjects.featureGraph.getEdge(curFeature, j) & AFeatureGraph.MASK_1_00001100) {
					case AFeatureGraph.EDGE_10:
						// don't select child
						childSelected = 0;
						visited[j] = 2;
						break;
					case AFeatureGraph.EDGE_11:
						// select child
						childSelected = 1;
						visited[j] = 2;
						break;
					case AFeatureGraph.EDGE_1Q:
						// ?
						if (visit == 1) {
							continue;
						}
						visited[j] = 1;
						childSelected = 2;
						break;
					default:
						continue;
					}
				} else {
					switch (sharedObjects.featureGraph.getEdge(curFeature, j) & AFeatureGraph.MASK_0_00110000) {
					case AFeatureGraph.EDGE_00:
						// don't select child
						childSelected = 0;
						visited[j] = 2;
						break;
					case AFeatureGraph.EDGE_01:
						// select child
						childSelected = 1;
						visited[j] = 2;
						break;
					case AFeatureGraph.EDGE_0Q:
						// ?
						if (visit == 1) {
							continue;
						}
						childSelected = 2;
						visited[j] = 1;
						break;
					default:
						continue;
					}
				}

				dfs_rec(visited, complete, j, curFeature, childSelected, selected);
			}
		}
	}

	private void dfs_rec(byte[] visited, boolean[] complete, int curFeature, int parentFeature, byte selected, boolean parentSelected) {
		final boolean incomplete = !complete[curFeature];
		for (int j = 0; j < visited.length; j++) {
			final byte visit = visited[j];
			byte childSelected = -1;
			if (visit == 0) {
				final byte edge = sharedObjects.featureGraph.getEdge(curFeature, j);
				switch (selected) {
				case 0:
					switch (edge & AFeatureGraph.MASK_0_00110000) {
					// visit = 0, not selected, implies not selected
					case AFeatureGraph.EDGE_00:
						visited[j] = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						childSelected = 0;
						break;
					// visit = 0, not selected, implies selected
					case AFeatureGraph.EDGE_01:
						visited[j] = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						childSelected = 1;
						break;
					// visit = 0, not selected, implies ?
					case AFeatureGraph.EDGE_0Q:
						visited[j] = 1;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_1Q : AFeatureGraph.EDGE_0Q);
						childSelected = 2;
						break;
					}
					break;
				case 1:
					switch (edge & AFeatureGraph.MASK_1_00001100) {
					// visit = 0, selected, implies not selected
					case AFeatureGraph.EDGE_10:
						visited[j] = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						childSelected = 0;
						break;
					// visit = 0, selected, implies selected
					case AFeatureGraph.EDGE_11:
						visited[j] = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						childSelected = 1;
						break;
					// visit = 0, selected, implies ?
					case AFeatureGraph.EDGE_1Q:
						visited[j] = 1;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_1Q : AFeatureGraph.EDGE_0Q);
						childSelected = 2;
						break;
					}
					break;
				case 2:
					if (edge > 0) {
						visited[j] = 1;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_1Q : AFeatureGraph.EDGE_0Q);
						childSelected = 2;
					}
					break;
				}
			} else if (visit == 1) {
				final byte edge = sharedObjects.featureGraph.getEdge(curFeature, j);
				switch (selected) {
				case 0:
					switch (edge & AFeatureGraph.MASK_0_00110000) {
					// visit = 1, not selected, implies not selected
					case AFeatureGraph.EDGE_00:
						visited[j] = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						childSelected = 0;
						break;
					// visit = 1, not selected, implies selected
					case AFeatureGraph.EDGE_01:
						visited[j] = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						childSelected = 1;
						break;
					}
					break;
				case 1:
					switch (edge & AFeatureGraph.MASK_1_00001100) {
					// visit = 1, selected, implies not selected
					case AFeatureGraph.EDGE_10:
						visited[j] = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_10 : AFeatureGraph.EDGE_00);
						childSelected = 0;
						break;
					// visit = 1, selected, implies selected
					case AFeatureGraph.EDGE_11:
						visited[j] = 2;
						sharedObjects.featureGraph.setEdge(parentFeature, j, parentSelected ? AFeatureGraph.EDGE_11 : AFeatureGraph.EDGE_01);
						childSelected = 1;
						break;
					}
					break;
				}
			}
			if (incomplete && childSelected >= 0) {
				dfs_rec(visited, complete, j, parentFeature, childSelected, parentSelected);
			}
		}
	}

}
