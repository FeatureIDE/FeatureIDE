


class Suite {
	        public void testBaseModel() {
                boolean[] rules = {false, false, false, true, false, false, false, false, false};
                boolean[] rules2 = {true, true, false, false,true, true, true, true, true};
                RuleSet r = new RuleSet(rules, rules2);
                GODLModel m = new GODLModel(10, 10, r);
                GODLModel m2 = new GODLModel(10, 10, r);
                m.setLifeform(0, 0, 1);
                m.setLifeform(1, 0, 1);
                m.setLifeform(0, 1, 1);
                m.setLifeform(2, 0, 1);
                m.setLifeform(3, 0, 1);
                m.setLifeform(4, 0, 1);
                m.setLifeform(5, 0, 1);
                m.setLifeform(8, 1, 1);
                m.setLifeform(9, 4, 1);
                m.setLifeform(9, 6, 1);
                m2.setLifeform(0, 0, 1);
                m2.setLifeform(1, 0, 1);
                m2.setLifeform(0, 1, 1);
                m2.setLifeform(2, 0, 1);
                m2.setLifeform(3, 0, 1);
                m2.setLifeform(4, 0, 1);
                m2.setLifeform(5, 0, 1);
                m2.setLifeform(8, 1, 1);
                m2.setLifeform(9, 4, 1);
                m2.setLifeform(9, 6, 1);
                m.nextGeneration();
                assertTrue(m.undoAvailable());
                assertTrue(!m.redoAvailable());
                m.undo();
                assertTrue(!m.undoAvailable());
                assertTrue(m.redoAvailable());
                m.redo();
                m.nextGeneration();
                m.nextGeneration();
                m.undo();
                m.undo();
                m.undo();
                assertEquals(m, m2);
                
                
            }
}