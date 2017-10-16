package br.ufal.ic.colligens.handler;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.jface.action.IContributionItem;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.actions.CompoundContributionItem;
import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;

import core.RefactoringType;

/**
 * @author Thiago Emmanuel
 *
 */
public class RefactorContributionItems extends CompoundContributionItem {

	public static String ID = "br.ufal.ic.colligens.RefactorContributionItems";

	public RefactorContributionItems() {
		super();
	}

	public RefactorContributionItems(String id) {
		super(id);
	}

	@Override
	protected IContributionItem[] getContributionItems() {
		final ArrayList<IContributionItem> citems = new ArrayList<IContributionItem>();

		for (final RefactoringType type : RefactoringType.values()) {

			final CommandContributionItemParameter parameters = new CommandContributionItemParameter(PlatformUI.getWorkbench().getActiveWorkbenchWindow(),
					RefactorContributionItems.ID, RefactorSelectionHandler.COMMAND_ID, CommandContributionItem.STYLE_PUSH);

			final Map<String, String> params = new HashMap<String, String>();

			params.put(RefactorSelectionHandler.PARM_ID, String.valueOf(type.name()));

			parameters.parameters = params;

			parameters.label = type.getLabel();

			final CommandContributionItem item = new CommandContributionItem(parameters);

			citems.add(item);
		}

		return citems.toArray(new IContributionItem[(citems.size())]);
	}
}
