package org.xtext.example.test;

import java.io.IOException;
import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.xtext.example.dJ.Class;
import org.xtext.example.dJ.Classm;
import org.xtext.example.dJ.Delta;
import org.xtext.example.dJ.ModifiesClass;
import org.xtext.example.dJ.Module;
import org.xtext.example.dJ.Program;
import org.xtext.example.lookup.AuxiliaryFunctions;
import org.xtext.example.util.ACST;

public class AuxiliaryFunctionsTest extends TestWithLoader{
	private AuxiliaryFunctions fixture;

	public AuxiliaryFunctionsTest(String name){
		super(name);
	}

	public void setUp(){
		super.setUp();
		this.fixture = new AuxiliaryFunctions();
	}

	protected void tearDown() throws Exception{
		this.fixture = null;
	}

	public void testCyclicAfter() throws IOException{
		Program p = getProgramFromString("features Base, co configurations Base, co; " +
										"core Base{} " +
										"delta A when co{}           delta B when co{} " +
										"delta C after A when co{}   delta D after B when co{} " +
										"delta E after F when co{}   delta F after G when co{} " +
										"delta G after E when co{}"); 
		Set<String> name = new HashSet<String>();
		name.add("A");
		name.add("B");
		name.add("C");
		name.add("D");
		for (Module module : p.getModulesList())
			if(module.getDelta() != null)
				if (name.contains(module.getDelta().getName()))
					assertFalse(this.fixture.cyclicAfter(module.getDelta(), new HashSet<String>()));
				else
					assertTrue(this.fixture.cyclicAfter(module.getDelta(), new HashSet<String>()));
	}
	
	public void testModifiedClassesAfter() throws IOException {
		Program p = getProgramFromString("features Base, co configurations Base, co; " +
										 "core co{class Alt{} class Aaa{} }" +
										 "delta A when Base{modifies class Alt{}} " +
										 "delta B when Base{modifies class Aaa{}} " +
										 "delta C after A when Base{remove Alt} " +
										 "delta D after C when co{adds class Alt{}} " +
										 "delta E after D when Base{modifies class Alt{}} " +
										 "delta F after E when Base{modifies class Alt{}}");
		
		Set<ModifiesClass> classesList = this.fixture.modifiedClassesAfter(p.getModulesList().get(1).getDelta(), p.getModulesList().get(1).getDelta().getClassesList().get(0).getModifies());
		ModifiesClass cm;
		assertTrue(p.getFeatures().getConfiguration() != null);
		assertTrue(classesList.size() == 1);
		cm = p.getModulesList().get(1).getDelta().getClassesList().get(0).getModifies();
		assertTrue(classesList.contains(cm));
		cm = p.getModulesList().get(2).getDelta().getClassesList().get(0).getModifies();
		assertFalse(classesList.contains(cm));
		cm = p.getModulesList().get(5).getDelta().getClassesList().get(0).getModifies();
		assertFalse(classesList.contains(cm));
		cm = p.getModulesList().get(6).getDelta().getClassesList().get(0).getModifies();
		assertFalse(classesList.contains(cm));
		
		
	}
	
	public void testCoreClasses() throws IOException{
		Program p = getProgramFromString("features Base, co configurations Base, co; " +
										"core Base{  " +
										"	class A{}" +
										"  class B{}" +
										"  class C{}" +
										"}" +
										"delta delta1 when co{" +
										"  adds class D{}" +
										"}");

		Set<String> nameClasses = new HashSet<String>();
		Set<String> nameClassesCore = new HashSet<String>();
		Collection<Class> classes = new LinkedList<Class>();
		nameClasses.add("A");
		nameClasses.add("B");
		nameClasses.add("C");
		nameClasses.add("D");
		for (Module module : p.getModulesList()) {
			classes = this.fixture.coreClasses(module);
			for (Class c : classes)
				nameClassesCore.add(c.getName());
		}
		for (String name : nameClasses)
			if (name.equals("D"))
				assertFalse(nameClassesCore.contains(name));
			else
				assertTrue(nameClassesCore.contains(name));
	}

	public void testAllDeltaLevel() throws IOException {
		Program p = getProgramFromString("features Base, co configurations Base, co; " +
										 "core co{}" +
										 "delta A when Base{} " +
										 "delta B when Base{} " +
										 "delta C after A when Base{} " +
										 "delta D after B when !co{} " +
										 "delta E after A, D when Base{} " +
										 "delta F after C, E when Base{}");

		Map<BigInteger, Set<Delta>> deltaLevel = this.fixture.allDeltaLevel(p);
		Set<String> deltaName = new HashSet<String>();
		for (BigInteger level : deltaLevel.keySet()) {
			deltaName.clear();
			for (Delta d : (Set<Delta>)deltaLevel.get(level))
				assertTrue(deltaName.add(d.getName()));
			if (level.equals(BigInteger.ONE)) {
				assertTrue(deltaName.contains("A"));
				assertTrue(deltaName.contains("B"));
			}
			if (level.equals(new BigInteger("2"))) {
				assertTrue(deltaName.contains("C"));
				assertTrue(deltaName.contains("D"));
				assertFalse(deltaName.contains("E"));
			}
			if (level.equals(new BigInteger("3"))) {
				assertTrue(deltaName.contains("E"));
				assertFalse(deltaName.contains("F"));
			}
			if (level.equals(new BigInteger("4")))
				assertTrue(deltaName.contains("F")); 
		}
	}
	
	public void testDeltaLevel() throws IOException{
		Program p = getProgramFromString("features Base, co configurations Base; " +
										"core co{} " +
										"delta A when Base{} " +
										"delta B after A when co{} " +
										"delta C after B when Base{} ");

		Map<BigInteger, Set<Delta>> deltaLevel = this.fixture.deltaLevel(p, p.getFeatures().getConfiguration().getFeatureList().get(0));
		Set<String> deltaName = new HashSet<String>();
		for (BigInteger level : deltaLevel.keySet()) {
			deltaName.clear();
			for (Delta d : (Set<Delta>)deltaLevel.get(level))
				assertTrue(deltaName.add(d.getName()));
			assertFalse(deltaName.contains("B"));
			if (level.equals(BigInteger.ONE)) {
				assertTrue(deltaName.contains("A"));
				assertFalse(deltaName.contains("C"));
			}
			if (level.equals(new BigInteger("2"))) {
				assertTrue(deltaName.contains("C"));
			//	assertFalse(deltaName.contains("D"));
			//	assertTrue(deltaName.contains("E"));
			}
			if (level.equals(new BigInteger("3"))) {
				assertFalse(deltaName.contains("E"));
				assertFalse(deltaName.contains("C"));
			}
			if (level.equals(new BigInteger("4")))
				assertFalse(deltaName.contains("F")); 
		}
	}
	
	public void testCyclicInheritance () throws IOException{
		Program p = getProgramFromString("features Base, co configurations Base, co; " +
				"core co{ " +
				"		class A extends B{}" +
				"		class B{}" +
				"} " +
				"delta A when Base{" +
				"					adds class C extends A{}" +
				"					modifies class B extending A{}" +
				"} " +
				"delta B when Base{adds class D{}} " +
				"delta C after B when Base{ adds class E extends D{}} " +
				"delta D after C when Base{adds class F extends E{}" +
				"							modifies class D extending F{}" +
				"							} "
				);
		Map <String, ACST> mapACST = new HashMap<String, ACST>();
		for(Module m : p.getModulesList())
			if(m.getNtype().equals("core"))
				for(Class c : m.getCore().getClassesList())
					mapACST.put(c.getName(),  new ACST(c));
			else for(Classm cm : m.getDelta().getClassesList())
				if(cm.getAction().equals("adds"))
					mapACST.put(cm.getAdds().getClass_().getName(),new ACST(cm.getAdds().getClass_()));
				else if(cm.getAction().equals("modifies"))
					mapACST.get(cm.getModifies().getClass_().getName()).setExtending(cm.getModifies().getExtends());

		assertTrue(this.fixture.cyclicInheritance("A", mapACST));
		assertTrue(this.fixture.cyclicInheritance("B", mapACST));
		assertFalse(this.fixture.cyclicInheritance("C", mapACST));
		assertFalse(this.fixture.cyclicInheritance("D", mapACST));
		assertFalse(this.fixture.cyclicInheritance("E", mapACST));
		assertFalse(this.fixture.cyclicInheritance("F", mapACST));
		
		
	}
	
	public void testIsParentClass () throws IOException{
		/*Program p = getProgramFromString("features Base, co configurations Base, co; " +
				"core co{ " +
				"		class A extends B{}" +
				"		class B{}" +
				"} " +
				"delta A when Base{" +
				"					adds class C extends A{}" +
				"					modifies class B{}" +
				"} " +
				"delta B when Base{adds class D{}} " +
				"delta C after B when Base{ adds class E extends D{}} " +
				"delta D after C when Base{adds class F extends E{}" +
				"							modifies class D{}" +
				"							} "
				);
		Map <String, CST> classApply = new HashMap<String, CST>();
		for(Module m : p.getModulesList())
			if(m.getNtype().equals("core"))
				for(Class c : m.getCore().getClassesList())
					classApply.put(c.getName(),  new CST(c));
			else for(Classm cm : m.getDelta().getClassesList())
				if(cm.getAction().equals("adds"))
					classApply.put(cm.getAdds().getClass_().getName(),new CST(cm.getAdds().getClass_()));
				else if(cm.getAction().equals("modifies"))
					if(cm.getModifies().getExtends() != null && classApply.get(cm.getModifies().getClass_().getName()) != null)
						classApply.get(cm.getModifies().getClass_().getName()).setExtending(cm.getModifies().getExtends());

		assertTrue(this.fixture.isParentClass("A", "B", classApply));
		assertFalse(this.fixture.isParentClass("B", "A", classApply));
		assertFalse(this.fixture.isParentClass("A", "C", classApply));
		assertFalse(this.fixture.isParentClass("D", "B", classApply));
		assertFalse(this.fixture.isParentClass("E", "F", classApply));
		assertTrue(this.fixture.isParentClass("F", "F", classApply));
		assertTrue(this.fixture.isParentClass("F", "E", classApply));		
		*/
		Program p = getProgramFromString("features Base, Inc configurations Base, Inc;"+
"core Base{"+
"  class A{"+
"    int a;"+
"    A(int a){"+
"     this.a = a;"+
"    }"+
"    int a(){return this.a;}"+
"  }"+
"}"+
"delta dInc when Inc{"+
"  adds class B{"+
"    int b;"+
"    B(int b){"+
"      this.b = b;"+
"    }"+
"    int b(){return this.b;}"+
"  }"+
"}");
		assertTrue(p.getFeatures().getConfiguration() != null);
	}
	
}