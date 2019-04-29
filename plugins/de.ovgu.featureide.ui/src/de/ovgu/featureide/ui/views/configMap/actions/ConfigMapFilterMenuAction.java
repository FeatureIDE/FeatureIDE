/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistributefilterMenu/or modify
 * it under the terms of the GNU LfilterMenueneral PufilterMenucense as published by
 * the FrefilterMenuare Foundation, either version 3 of the License, or
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
package de.ovgu.featureide.ui.views.configMap.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.ActionContributionItem;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuCreator;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Menu;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.ui.views.configMap.IConfigurationMapFilter;
import de.ovgu.featureide.ui.views.configMap.IConfigurationMapFilterable;

/**
 * @author Paul Maximilian Bittner
 * @author Antje Moench
 */
public class ConfigMapFilterMenuAction extends Action implements IMenuCreator {

	private Menu filterMenu = null;
	private final IConfigurationMapFilterable filterable;
	private final ConfigMapFilterAction[] filterActions;

	public ConfigMapFilterMenuAction(IConfigurationMapFilterable filterable, final IConfigurationMapFilter... filters) {
		super("Filters", IAction.AS_DROP_DOWN_MENU);
		this.filterable = filterable;
		setToolTipText("Filter Features");
		setMenuCreator(this);

		filterActions = new ConfigMapFilterAction[filters.length];
		for (int i = 0; i < filters.length; i++) {
			final IConfigurationMapFilter filter = filters[i];
			filterActions[i] = new ConfigMapFilterAction(filter, this.filterable);
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.IMenuCreator#getMenu(org.eclipse.swt.widgets.Control)
	 */
	@Override
	public Menu getMenu(Control parent) {
		if (filterMenu == null) {
			filterMenu = new Menu(parent);
			for (int i = 0; i < filterActions.length; i++) {
				final ConfigMapFilterAction filterAction = filterActions[i];
				filterAction.initializeImage(FMUIPlugin.getImage(filterAction.getFilter().getImagePath()));

				final ActionContributionItem contributionItem = new ActionContributionItem(filterAction);
				contributionItem.fill(filterMenu, -1 /* means insert at end */);
			}
		}

		return filterMenu;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.IMenuCreator#getMenu(org.eclipse.swt.widgets.Menu)
	 */
	@Override
	public Menu getMenu(Menu parent) {
		return filterMenu;
	}

	@Override
	public void dispose() {}
}
