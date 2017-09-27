/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Collection;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.conf.worker.base.AWorkerThread;
import de.ovgu.featureide.fm.core.editing.remove.FeatureRemover;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.ConsoleMonitor;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 *
 * @author Sebastian Krieter
 */
public class RemoveThread extends AWorkerThread<Collection<String>> {

	private static class SharedObjects {

		public final Collection<Node> nodeList;
		public final Node completeNode;

		public SharedObjects(Collection<Node> nodeList, Node completeNode) {
			this.nodeList = nodeList;
			this.completeNode = completeNode;
		}

	}

	private final SharedObjects sharedObjects;

	public RemoveThread(IMonitor monitor, Collection<Node> nodeList, Node completeNode) {
		super(monitor);
		sharedObjects = new SharedObjects(nodeList, completeNode);
	}

	private RemoveThread(RemoveThread oldThread) {
		super(oldThread);
		sharedObjects = new SharedObjects(oldThread.sharedObjects.nodeList, oldThread.sharedObjects.completeNode);
	}

	@Override
	protected void work(Collection<String> removeFeatures) {
		final IMonitor wm = new ConsoleMonitor();
		final FeatureRemover remover = new FeatureRemover(sharedObjects.completeNode, removeFeatures);
		final Node subNode = remover.createNewClauseList(LongRunningWrapper.runMethod(remover, wm));
		if ((subNode.getChildren().length > 0) && !((subNode.getChildren().length == 1) && (subNode.getChildren()[0].getChildren().length == 0))) {
			addNode(subNode);
		}
	}

	private synchronized void addNode(Node subNode) {
		sharedObjects.nodeList.add(subNode);
	}

	@Override
	protected RemoveThread newThread() {
		return new RemoveThread(this);
	}

}
