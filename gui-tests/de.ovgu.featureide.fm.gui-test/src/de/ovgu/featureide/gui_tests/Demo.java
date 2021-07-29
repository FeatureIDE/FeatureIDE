package de.ovgu.featureide.gui_tests;
import org.eclipse.jface.bindings.keys.KeyStroke;
import org.eclipse.swt.SWT;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.eclipse.finder.widgets.SWTBotView;
import org.eclipse.swtbot.eclipse.gef.finder.widgets.SWTBotGefEditor;
import org.eclipse.swtbot.swt.finder.SWTBot;
import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.junit.SWTBotJunit4ClassRunner;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTree;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotTreeItem;
import org.junit.AfterClass;
import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;

@RunWith(SWTBotJunit4ClassRunner.class)
public class Demo {

    private static SWTWorkbenchBot bot;

    @BeforeClass
    public static void beforeClass() throws Exception {

        bot = new SWTWorkbenchBot();
    }

    @Test
    public void loadCarFM() {
        
        bot.viewByTitle("Welcome").close();
        
        bot.menu("File").menu("New").menu("Example...").click();
    
        bot.tree().getTreeItem("FeatureIDE").getNode("FeatureIDE Examples").select();
        bot.button("Next >").click();
        
        bot.cTabItem("Feature Modeling").activate();
        bot.tree().getTreeItem("FeatureIDE Format").expand();
        bot.tree().getTreeItem("FeatureIDE Format").getNode("Car").check();
        bot.button("Finish").click();   
        
        bot.viewByTitle("Project Explorer").setFocus();
        
        SWTBotView view = bot.viewByTitle("Project Explorer");
        SWTBotTree tree = new SWTBot(view.getWidget()).tree(0);
        SWTBotTreeItem projectItem = tree.getTreeItem("Car");
        
        projectItem.expand().getNode("model.xml").doubleClick();
        
        //Confirm Constraint View Dialog
        bot.button("Yes").click();
                
        SWTBotGefEditor editor = new SWTBotGefEditor(bot.editorByTitle("Car Model").getReference(), bot);
        SWTBotView constraintView = bot.viewByTitle("Feature Model Constraints");
        
        editor.getEditPart("Car").select();
        editor.clickContextMenu("Create Feature Above");
    
        editor.bot().text("NewFeature").setText("Audi").pressShortcut(KeyStroke.getInstance(SWT.CR));
    
        testSaveRemovesDirty(editor);
        
        //FIXME: Find better option to remove focus from feature
        editor.click(10, 10);

        editor.clickContextMenu("Create Constraint");
        
        bot.table().getTableItem("Radio").doubleClick();
        bot.button("Create Constraint").click();
        
        try {
            constraintView.bot().tree().getTreeItem("Radio");
        }catch(WidgetNotFoundException wnfe) {
            Assert.fail("Constraint \"Radio\" was not created (before save)");
        }
        
        testSaveRemovesDirty(editor);
        
        bot.menu("Edit").menu("Undo Create Constraint").click();
        
        try {
            constraintView.bot().tree().getTreeItem("Radio");
            Assert.fail("Constraint \"Radio\" was not removed (before save)");
        }catch(WidgetNotFoundException wnfe) {
            //Intended behavior
        }       

        testSaveRemovesDirty(editor);               

        bot.menu("Edit").menu("Redo Create Constraint").click();
        
        //FIXME: This should not be necessary
        constraintView = bot.viewByTitle("Feature Model Constraints");
        
        try {
            constraintView.bot().tree().getTreeItem("Radio");
        }catch(WidgetNotFoundException wnfe) {
            Assert.fail("Constraint \"Radio\" was not created (before save)");
        }
        
        testSaveRemovesDirty(editor);
    }

    public void testSaveRemovesDirty(SWTBotGefEditor editor) {

        Assert.assertTrue(editor.isDirty());
        editor.save();
        Assert.assertFalse(editor.isDirty());
    }
    
    @AfterClass
    public static void sleep() {
        bot.sleep(1000);
    }
}