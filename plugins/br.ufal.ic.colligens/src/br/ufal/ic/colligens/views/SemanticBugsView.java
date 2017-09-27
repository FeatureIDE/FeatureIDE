package br.ufal.ic.colligens.views;

import static de.ovgu.featureide.fm.core.localization.StringTable.SEMANTIC_BUGS___COLLIGENS;

import java.util.List;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.part.ViewPart;

import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.semanticbugs.SemanticBugsViewController;
import br.ufal.ic.colligens.models.cppchecker.CppCheckerFileLogs;

public class SemanticBugsView extends ViewPart {

	public static final String ID = Colligens.PLUGIN_ID + ".views.SemanticBugsView";

	private final SemanticBugsViewController viewController;

	public SemanticBugsView() {
		viewController = SemanticBugsViewController.getInstance();
		viewController.setView(this);
		setTitleToolTip(SEMANTIC_BUGS___COLLIGENS);
	}

	@Override
	public void createPartControl(Composite parent) {
		viewController.createPartControl(parent);
	}

	public void setInput(List<CppCheckerFileLogs> logs) {
		viewController.setInput(logs);
	}

	@Override
	public void setFocus() {
		viewController.setFocus();
	}

}
