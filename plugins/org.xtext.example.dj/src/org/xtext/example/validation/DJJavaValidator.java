package org.xtext.example.validation;

import java.math.BigInteger;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.EcoreUtil2;
import org.eclipse.xtext.validation.Check;
import org.xtext.example.dJ.AddsField;
import org.xtext.example.dJ.AddsMethod;
import org.xtext.example.dJ.Argument;
import org.xtext.example.dJ.Class;
import org.xtext.example.dJ.Classm;
import org.xtext.example.dJ.Condition;
import org.xtext.example.dJ.Config;
import org.xtext.example.dJ.Constructor;
import org.xtext.example.dJ.ConstructorFieldExpression;
import org.xtext.example.dJ.Core;
import org.xtext.example.dJ.DJPackage;
import org.xtext.example.dJ.Delta;
import org.xtext.example.dJ.Expression;
import org.xtext.example.dJ.Field;
import org.xtext.example.dJ.Import;
import org.xtext.example.dJ.Method;
import org.xtext.example.dJ.MethodBody;
import org.xtext.example.dJ.Methodm;
import org.xtext.example.dJ.ModifiesClass;
import org.xtext.example.dJ.ModifiesMethod;
import org.xtext.example.dJ.Module;
import org.xtext.example.dJ.New;
import org.xtext.example.dJ.Parameter;
import org.xtext.example.dJ.Program;
import org.xtext.example.dJ.RemovesField;
import org.xtext.example.dJ.RemovesMethod;
import org.xtext.example.dJ.TerminalExpression;
import org.xtext.example.dJ.Type;
import org.xtext.example.linking.DjResourceFactory;
import org.xtext.example.lookup.AuxiliaryFunctions;
import org.xtext.example.type.CheckReturnType;
import org.xtext.example.type.ClassType;
import org.xtext.example.util.ACST;
import org.xtext.example.util.CST;
import org.xtext.example.util.ContainingModifiesMethodFinded;
import org.xtext.example.util.ContainingModuleFinded;
import org.xtext.example.util.ContainingProgramFinded;
import org.xtext.example.util.DJIdeProperties;
import org.xtext.example.util.ValidationStatus;

public class DJJavaValidator extends AbstractDJJavaValidator{
	AuxiliaryFunctions auxiliary = new AuxiliaryFunctions();
	Set<String> classNotConstructor = new HashSet<String>();
	/*
	 * Segnala errori di ereditarietˆ ciclica tra classi di un modulo core. 
	 */
	@Check
	public void checkInheritanceCore(Core core){
		if(deactivateValidator()) return;
		
		for (Class c : core.getClassesList()) {
			if (c.getName().equals(c.getExtends().getName())) {
				error("Cycle detected: the class " + c.getName() + " cannot extend itself", c, DJPackage.CLASS__EXTENDS);
				return;
			}
			
			Class a = c;
			Collection<String> classesList = new LinkedList<String>();
			classesList.add(a.getName());
			while ((a.getExtends() != null) && (!classesList.contains(a.getExtends().getName()))) {
				classesList.add(a.getExtends().getName());
				a = a.getExtends();
			}
			if (a.getExtends() != null)
				error("Cycle detected: the class " + c.getName() + " cannot extend one of its own member classes", c, DJPackage.CLASS__EXTENDS);
		}
	}

	/*
	 * Segnala errori di ereditarietˆ ciclica tra classi di delta moduli (senza applicare delta effettivamente i delta moduli)
	 * Segnala errori di tipo dei metodi di una classe rispetto alle sue "parent-class" nel tipo di ritorno con metodi che hanno lo stesso nome
	 * Segnala errori di tipo dei campi di una classe rispetto alle sue "parent-class" con campi che hanno lo stesso nome 
	 * Segnala errori di type uniform
	 */
	@Check
	public void checkGeneral(Program p){
		if(deactivateValidator()) return;
		classNotConstructor.add("AllObject");
		
		Map<String, ACST> map = checkTypeUniform(p);
		
		//inizio blocco
		/* Questo blocco di 4 righe serve per segnare tutte le classi 
		 * che non hanno costruttore in nessuna configurazione
		 */
		for(String name : map.keySet())
			if(map.get(name).getConstructor().size() == 0)
				classNotConstructor.add(name);
		//fine blocco
		
		Set<Set<String>> inheritance = new HashSet<Set<String>>();
		Collection<Module> moduleList = new LinkedList<Module>();
		Collection<Import> importList = p.getImports();
		for (Import imp : importList) {
			Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
			Program current = (Program)resource.getContents().get(0);
			moduleList.addAll(current.getModulesList());
		}
		moduleList.addAll(p.getModulesList());
		for (String name : map.keySet()) {
			inheritance.addAll(checkInheritance(name, map));
			for (Module m : moduleList){	
				if(m.getNtype() != null){
					if (m.getNtype().equals("core")) {
						for (Class c : m.getCore().getClassesList()) {
							if (c.getName() == name){
								for (Set<String> temp : inheritance) {
									String classes = "";
									if ((c.getExtends() != null) && (temp.contains(c.getExtends().getName()))) {
										for (String temp2 : temp) {
											classes = classes + " " + temp2;
										}
										error("Error cyclic inheritance " + classes, c, Integer.valueOf(0));
									}
									ACST originalACST = (ACST)map.get(c.getName());
									ACST tempACST = map.get(temp);
									checkMethodFieldInheritance(originalACST, tempACST);
								}
							}
						}
					}
					else{
						for (Classm cm : m.getDelta().getClassesList()){
							if (cm.getAction().equals("adds")) {
								if (cm.getAdds().getClass_().getName().equals(name)){
									for (Set<String> temp : inheritance) {
										String classes = "";
										if ((cm.getAdds().getClass_().getExtends() != null) && (temp.contains(cm.getAdds().getClass_().getExtends().getName()))) {
											for (String temp2 : temp)
												classes = classes + " " + temp2; 
											error("Error cyclic inheritance " + classes, cm.getAdds(), Integer.valueOf(0));
										}
										ACST originalACST = map.get(cm.getAdds().getClass_().getName());
										ACST tempACST = map.get(temp);
										checkMethodFieldInheritance(originalACST, tempACST);
									}
								}
							} else {
								if ((cm.getAction().equals("modifies")) && 
										(cm.getModifies().getClass_().getName().equals(name))){
									for (Set<String> temp : inheritance) {
										String classes = "";
										if ((cm.getModifies().getExtends() != null) && (temp.contains(cm.getModifies().getExtends().getName()))) {
											for (String temp2 : temp)
												classes = classes + " " + temp2; 
											error("Error cyclic inheritance " + classes, cm.getModifies(), Integer.valueOf(19));
										}
										ACST originalACST = map.get(cm.getModifies().getClass_().getName());
										ACST tempACST = map.get(temp);
										checkMethodFieldInheritance(originalACST, tempACST);
									}
								}
							}
						}
					}
				}
			}
		}
	}

	private void checkMethodFieldInheritance(ACST originalACST, ACST tempACST) {
		if(deactivateValidator()) return;
		if ((originalACST != null) && (tempACST != null)) {
			for (String method : originalACST.getMethods().keySet())
				if (tempACST.getMethods().get(method) != null) {
					String method1ReturnType = originalACST.getMethods().get(method).getReturntype().getBasic();
					if (method1ReturnType == null)
						method1ReturnType = originalACST.getMethods().get(method).getReturntype().getClassref().getName();
					String method2ReturnType = tempACST.getMethods().get(method).getReturntype().getBasic();
					if (method2ReturnType == null)
						method2ReturnType = tempACST.getMethods().get(method).getReturntype().getClassref().getName();
					if (method1ReturnType.equals(method2ReturnType)) {
						error("The return type is incompatible with the same method defined in the superclasses", (EObject)originalACST.getMethods().get(method), Integer.valueOf(0));
					}
					List<Parameter> methods1 = originalACST.getMethods().get(method).getParams();
					List<Parameter> methods2 = tempACST.getMethods().get(method).getParams();
					if(methods1.size() == methods2.size()){
						int c = 0;
						for (Parameter param : methods1){
							ClassType ct1 = new ClassType();
							ClassType ct2 = new ClassType();
							ct1.setType(param.getType());
							ct2.setType(methods2.get(c++).getType());
							if(ct2.getBasicType() != null){
								if(!ct2.getBasicType().equals(ct1.getBasicType()))
									error("The parameters type are incompatible with the same method defined in the superclasses", (EObject)originalACST.getMethods().get(method), Integer.valueOf(0));
							}else
								if(ct1.getClassType() != null && ct2.getClassType() != null){
									if(!ct2.getClassType().getName().equals(ct1.getClassType().getName()))
										error("The parameters type are incompatible with the same method defined in the superclasses", (EObject)originalACST.getMethods().get(method), Integer.valueOf(0));
								}else
									error("The parameters type are incompatible with the same method defined in the superclasses", (EObject)originalACST.getMethods().get(method), Integer.valueOf(0));
							
						}
					}else 
						error("The parameters number is incompatible with the same method defined in the superclasses", (EObject)originalACST.getMethods().get(method), Integer.valueOf(0));
				}
			for (String field : originalACST.getFields().keySet()){
				if (tempACST.getFields().get(field) != null) {
					String field1ReturnType = originalACST.getFields().get(field).getType().getBasic();
					if (field1ReturnType == null)
						field1ReturnType = originalACST.getFields().get(field).getType().getClassref().getName();
					String field2ReturnType = tempACST.getFields().get(field).getType().getBasic();
					if (field2ReturnType == null)
						field2ReturnType = tempACST.getFields().get(field).getType().getClassref().getName();
					if (field1ReturnType.equals(field2ReturnType)) {
						error("The same field has already been defined with different type in some superclass", (EObject)originalACST.getMethods().get(field), Integer.valueOf(0));
					}
				}
			}
		}
	}
	
	/*Questo metodo viene utilizzato dal metodo checkGeneral e segnala tutti gli errori di typ-uniform*/
	private Map<String, ACST> checkTypeUniform(Program p) {		
		if(deactivateValidator()) return null;
		Map<BigInteger, Set<Delta>> deltaMapLevel = auxiliary.allDeltaLevel(p);
		LinkedList<Module> moduleList = new LinkedList<Module>();
		moduleList.addAll(p.getModulesList());
		Map<String, ACST> classMapApply = new HashMap<String, ACST>();
		Program current;
		for (Import imp : p.getImports()) {
			Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
			current = (Program)resource.getContents().get(0);
			moduleList.addAll(current.getModulesList());
		}
		for (Module m : moduleList)
			if (m.getNtype() != null)
				if (m.getNtype().equals("core")) { 
					for (Class c : m.getCore().getClassesList()){
						ACST acst = new ACST(c);
						classMapApply.put(c.getName(), acst); 
						for(Field field : c.getField())
							if("void".equals(field.getType().getBasic()))
								if(p.getModulesList().contains(m) )
									error("void is an invalid type for variables " + field.getReference().getName(), field, DJPackage.FIELD);
					}	
				}
		for (BigInteger b : deltaMapLevel.keySet()){
			for (Delta d : deltaMapLevel.get(b)) {
				for (Classm cm : d.getClassesList())
					if (cm.getAction().equals("adds")) {
						Class c = cm.getAdds().getClass_();
						if (classMapApply.containsKey(c.getName())) {
							ACST classTemp = classMapApply.get(c.getName());
							if ( c.getExtends() != null && classTemp.setExtending(c.getExtends()) )
									if(auxiliary.cyclicInheritance(c.getName(), classMapApply))
										error("Error in uniform-type on the inheritance", cm.getAdds().getClass_(), Integer.valueOf(1));
							if (c.getConstructor() != null && c.getConstructor().size() != 0)
								classTemp.setConstructors(c.getConstructor().get(0));
							for (Method m : c.getMethod())
								if (!classTemp.setMethods(m))
									error("Error in uniform-type of this method", m, Integer.valueOf(1));
							for (Field field : c.getField()){
								if("void".equals(field.getType().getBasic()))
									error("void is an invalid type for variable " + field.getReference().getName(), field, DJPackage.FIELD);
								if (!classTemp.setFields(field))
									error("Error in uniform-type of this field", field, Integer.valueOf(0));
							}
						}else {
							classMapApply.put(c.getName(), new ACST(c));
						}
					}else if (cm.getAction().equals("modifies")) {
						Class c = cm.getModifies().getClass_();
						if (!classMapApply.containsKey(c.getName())) {
							Program pTemp = new ContainingProgramFinded().lookup(cm.getModifies());
							if(p.equals(pTemp))
								error("Cannot modify this class, it doesn't exist", cm.getModifies(), Integer.valueOf(0));
						}else {
							ACST classTemp = classMapApply.get(c.getName());
							if (cm.getModifies().getExtends() != null) {
								classTemp.setExtending(cm.getModifies().getExtends());
								if (auxiliary.cyclicInheritance(c.getName(), classMapApply))
									error("Error in uniform-type on the inheritance", cm.getModifies(), Integer.valueOf(1));
							}
							if(cm.getModifies().getConstructor() != null){
								classTemp.setConstructors(cm.getModifies().getConstructor());
							}
							Methodm methodm = cm.getModifies().getMethod();
							for (AddsMethod method : methodm.getAddsList())
								if (!classTemp.setMethods(method.getMethod()))
									error("Error in uniform-type of this method", method.getMethod(), DJPackage.METHOD__REFERENCE);
							for (ModifiesMethod method : methodm.getModifiesList())
								if (!classTemp.modifiesMethod(method, method.getMethodRef().getName()))
									error("Error in uniform-type of this method", method, DJPackage.METHOD__REFERENCE);
							for (AddsField field : cm.getModifies().getField().getAddsList()) {
								if("void".equals(field.getField().getType().getBasic()))
									error("void is an invalid type for variable " + field.getField().getReference().getName(), field, DJPackage.FIELD);
								if (!classTemp.setFields(field.getField())) {
									error("Error in uniform-type of this field", field.getField(), Integer.valueOf(0));
								}
							}
							classMapApply.put(c.getName(), classTemp);
						}
					}	
			} 
		}
		return classMapApply;
	}

	/*Questo metodo � usato dal metodo checkGeneral per avere per ogni classe la lista delle proprie "parent-class"*/
	private Set<Set<String>> checkInheritance(String name, Map<String, ACST> map) {
		if(deactivateValidator()) return null;
		Set<Set<String>> inheritance = new HashSet<Set<String>>();
		for (String extending : map.get(name).getExtending()) {
			Set<String> temp = new HashSet<String>();
			temp.add(name);
			inheritance.addAll(inheritance(temp, extending, map));
			temp.remove(name);
		}
		return inheritance;
	}

	/*Questo metodo � usato dal metodo checkInheritance e segnala errori di tipo con le classi parent*/
	private Set<Set<String>> inheritance(Set<String> originalName, String name, Map<String, ACST> map){
		if(deactivateValidator()) return null;
		Set<String> tempName = new HashSet<String>();
		tempName.add(name);
		tempName.addAll(originalName);
		originalName = tempName;
		Set<Set<String>> classes = new HashSet<Set<String>>();
		int i = 0;
		for (String extending : map.get(name).getExtending()) {
			boolean cyclic = false;
			Set<String> temp = new HashSet<String>();
			for (String visited : originalName)
				if ((cyclic) && (i == 0)) 
					temp.add(visited);
				else if (visited.equals(extending)) {
					if (i == 0)
						temp.add(visited);
					cyclic = true;
				} else {
					i++;
				}
			classes.add(temp);
			if (!cyclic) {
				classes.addAll(inheritance(originalName, extending, map));
			}
		}
		for (String visited : originalName) {
			ACST parent = map.get(name);
			ACST original = map.get(visited);
			for (String fName : parent.getFields().keySet()) {
				if (original.getFields().get(fName) != null)
					if (original.getFields().get(fName).getType().getBasic() != null)
						if (parent.getFields().get(fName).getType().getBasic() != null){
							if (!original.getFields().get(fName).getType().getBasic().equals(parent.getFields().get(fName).getType().getBasic()))
								error("The same field has already been defined with different type in some superclass", (EObject)original.getFields().get(fName), Integer.valueOf(8));
						}else
							error("The same field has already been defined with different type in some superclass", (EObject)original.getFields().get(fName), Integer.valueOf(8));
					else if (parent.getFields().get(fName).getType().getBasic() == null){
						if (!original.getFields().get(fName).getType().getClassref().getName().equals(((Field)parent.getFields().get(fName)).getType().getClassref().getName()))
							error("The same field has already been defined with different type in some superclass", (EObject)original.getFields().get(fName), Integer.valueOf(8));
					}else
						error("The same field has already been defined with different type in some superclass", (EObject)original.getFields().get(fName), Integer.valueOf(8));
			}
			for (String fName : parent.getMethods().keySet()) {
				if (original.getMethods().get(fName) != null)
					if (original.getMethods().get(fName).getReturntype().getBasic() != null)
						if (parent.getMethods().get(fName).getReturntype().getBasic() != null){
							if (!original.getMethods().get(fName).getReturntype().getBasic().equals(((Method)parent.getMethods().get(fName)).getReturntype().getBasic()))
								error("Error in type of this method, look the type of the same method in the class parent", (EObject)original.getMethods().get(fName), Integer.valueOf(1));
						}else
							error("Error in type of this method, look the type of the same method in the class parent", (EObject)original.getFields().get(fName), Integer.valueOf(1));
					else if (parent.getMethods().get(fName).getReturntype().getBasic() == null){
						if (!original.getMethods().get(fName).getReturntype().getClassref().getName().equals(((Method)parent.getMethods().get(fName)).getReturntype().getClassref().getName()))
							error("Error in type of this method, look the type of the same method in the class parent", (EObject)original.getMethods().get(fName), Integer.valueOf(1));
					}else
						error("Error in type of this method, look the type of the same method in the class parent", (EObject)original.getMethods().get(fName), Integer.valueOf(1));
			}
		}
		return classes;
	}	

	/*
	 * Questo metodo segnala errori nella struttura del complesso di files presenti
	 * Segnala quindi una eventuale mancanza o eccesso di moduli core o features e relative configurazioni
	 * Segnala anche eventuali errori delle clausole when dei delta rispetto al modulo core
	 */
	@Check
	public void checkModule(Program p) {
		if(deactivateValidator()) return;
		
		Collection<Import> importList = new LinkedList<Import>();
		Collection<Module> moduleList = new LinkedList<Module>();
		moduleList.addAll(p.getModulesList());
		importList.addAll(p.getImports());
		boolean existFeature = false;
		for (Import imp : importList) {
			Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
			if(resource.getContents().size() != 0){
				Program current = (Program)resource.getContents().get(0);
				moduleList.addAll(current.getModulesList());
				if(current.getFeatures() != null)
					existFeature = true;
			}
		}
		if(p.getFeatures() != null)
			if(existFeature)
				error("Cannot add another feature list, one alerady exists", p.getFeatures(), DJPackage.FEATURES__FEATURES_LIST);
		boolean found = false;
		boolean foundCore = false;
		for (Module m : p.getModulesList()) {
			found = false;
			for (Module m2 : moduleList)
				if(m.getNtype() != null)
					if ((m.getNtype().equals("delta")) && (m2.getNtype().equals("delta"))) {
						if (m.getDelta().getName().equals(m2.getDelta().getName()))
							if (found) error("Cannot add this delta module, it already exists", m.getDelta(), Integer.valueOf(0)); 
							else
								found = true;
					}else if (m.getNtype().equals("core")){
						foundCore = true;
						if(m2.getNtype().equals("core")){
							if (found) 
								error("Cannot add another core module, one already exists", m.getCore(), Integer.valueOf(0));
							else 
								found = true;
						}
					}else if((m2.getNtype().equals("core")) && m.getNtype().equals("delta")){
						foundCore = true;
						boolean condition = true;
						for(Condition cond : m.getDelta().getCondition())
							if(!auxiliary.validCondition(cond, m2.getCore().getName())){
								condition = false;
							}
						if(condition)
							error("Cannot use this where-condition for the delta module", m.getDelta(), DJPackage.DELTA__CONDITION);
					}
		}
		if(!foundCore) 
			if(p.getModulesList() != null)
				error("Add a core module, it doesn't exist", p.getModulesList().get(0), DJPackage.MODULE);
	}

	/*
	 * Questo metodo segnala eventuali errori di ciclicitˆ delle clausule after dei delta moduli.
	 */
	@Check
	public void checkAfterCondition(Delta d) {
		if(deactivateValidator()) return;
		
		if (auxiliary.cyclicAfter(d, new HashSet<String>()))
			error("Cannot add this after condition, it creates a cyclic after condition", d, Integer.valueOf(14));
	}

	/*
	 * Questo metodo controlla che non vi siano metodi o campi ripetuti in una stessa classe
	 * e che non vi siano classi ripetute dentro al modulo core se necessario ne segnala l'errore.
	 * Richiama anche il metodo sottostante checkDeltaClass. 
	 */
	@Check
	public void checkClass(Program p) {
		if(deactivateValidator()) return;
		
		Collection<Module> moduleList = new LinkedList<Module>();
		Set<String> classList = new HashSet<String>();
		moduleList.addAll(p.getModulesList());
		for (Module m : moduleList){
			if(m.getNtype() != null){
				if (m.getNtype().equals("delta")){
					checkDeltaClass(m);
				}else{
					for (Class c : m.getCore().getClassesList()) {
						Set<String> methodList = new HashSet<String>();
						Set<String> fieldList = new HashSet<String>();
						for (Method method : c.getMethod())
							if (!methodList.add(method.getReference().getName()))
								error("Cannot add this method, it already exists", method, Integer.valueOf(1));
						for (Field field : c.getField())
							if (!fieldList.add(field.getReference().getName()))
								error("Cannot add this field, it already exists", field, Integer.valueOf(1));
						if (!classList.add(c.getName()))
							error("Cannot add this class, it already exists", c, Integer.valueOf(6));
					}
				}
			}
		}
	}
	
	/*
	 * Questo metodo controlla che non vi sia pi� di un'operazione su ciascuna classe in uno stesso delta modulo.
	 * Controlla anche che non vi siano pi� operazioni (a parte un'eliminazione ed un'aggiunta) sullo stesso campo o metodo in ogni classe.
	 * Se necessario segnala l'errore
	 */
	private void checkDeltaClass(Module m){
		if(deactivateValidator()) return;
		Collection<Classm> classmList = new LinkedList<Classm>();
		Set<String> classmSet = new HashSet<String>();
		classmList.addAll(m.getDelta().getClassesList());
		for (Classm c : classmList) {
			if ((c.getAction().equals("remove")) && (!classmSet.add(c.getRemove().getClass_().getName())))
				error("Cannot remove this class, it is already in use in this delta module", c.getRemove(), Integer.valueOf(0));
			if (c.getAction().equals("modifies"))
				if (!classmSet.add(c.getModifies().getClass_().getName()))
					error("Cannot modifie this class, it is already in use in this delta module", c.getModifies(), Integer.valueOf(0));
				else{
					Set<String> methodList = new HashSet<String>();
					Set<String> fieldList = new HashSet<String>();
					for (AddsMethod method : c.getModifies().getMethod().getAddsList()){
						if (!methodList.add(method.getMethod().getReference().getName()))
							error("Cannot add this method, it already exists in this class", method, Integer.valueOf(1));
					}
					for (AddsField field : c.getModifies().getField().getAddsList())
						if (!fieldList.add(field.getField().getReference().getName()))
							error("Cannot add this field, it already exists", field, Integer.valueOf(1));
				}
			if (c.getAction().equals("adds"))
				if (!classmSet.add(c.getAdds().getClass_().getName())) {
					error("Cannot adds this class, it is already in use in this delta module", c.getAdds(), Integer.valueOf(0));
				}else {
					Set<String> methodList = new HashSet<String>();
					Set<String> fieldList = new HashSet<String>();
					for (Method method : c.getAdds().getClass_().getMethod())
						if (!methodList.add(method.getReference().getName()))
							error("Cannot add this method, it already exists", method, Integer.valueOf(1));
					for (Field field : c.getAdds().getClass_().getField())
						if (!fieldList.add(field.getReference().getName()))
							error("Cannot add this field, it already exists", field, Integer.valueOf(1));
				}
		}
	}

	/* richiama i due metodi sotto checkMethodModification e checkFieldRemove*/
	@Check
	public void checkMethodField(Classm c) {
		if(deactivateValidator()) return;
		
		checkMethodModification(c);
		checkFieldRemove(c);
	}

	/*
	 * Questo metodo segnala se un metodo viene rimosso pi� di una volta in una classe
	 * Qeusto metodo segnala se un metodo che si vuole modificare � giˆ stato modificato o rimosso
	 * nella classe stessa. 
	 */
	private void checkMethodModification(Classm c) {
		if(deactivateValidator()) return;
		if (c.getAction().equals("modifies")) {
			Set<String> names = new HashSet<String>();
			for (RemovesMethod mthd : c.getModifies().getMethod().getRemoveList()) {
				if (!names.add(mthd.getMethodRef().getName())) {
					error("Cannot remove this method, it has already been removed in this class", mthd, Integer.valueOf(0));
				}
			}
			for (ModifiesMethod mthd : c.getModifies().getMethod().getModifiesList())
				if (!names.add(mthd.getMethodRef().getName()))
					error("Cannot modify this method, it has already been removed or modified in this class", mthd, DJPackage.METHOD__REFERENCE); 
		}
	}
	
	/*
	 * Questo metodo segnala se un campo viene eliminato pi� di una volta in una stessa classe. 
	 */
	private void checkFieldRemove(Classm c) {
		if(deactivateValidator()) return;
		if (c.getAction().equals("modifies")) {
			Set<String> names = new HashSet<String>();
			for (RemovesField f : c.getModifies().getField().getRemoveList())
				if (!names.add(f.getFieldRef().getName()))
					error("Cannot remove this field, it has already been removed in this class", f, Integer.valueOf(0));
		}
	}
	
	/*
	 * Questo metodo segnala errori di conflitto tra delta moduli quando due o pi� delta moduli
	 * su di uno stesso livello dell'after-DAG applicano operazioni sulla stessa classe.
	 * Nel caso ci siano pi� modifiche ad una classe cmq il controllo e lasciato ai metodi sotto
	 * checkMethodConflict e checkFieldConflict.
	 */
	@Check
	public void checkConflict(Program p) {
		if(DJIdeProperties.getValidationStatus() != ValidationStatus.VALIDATE_ALL) return;
		
		Collection<Config> configList = new LinkedList<Config>();
		if(p.getFeatures() != null && p.getFeatures().getConfiguration() != null)
			configList = p.getFeatures().getConfiguration().getFeatureList();
		else
			for (Import imp : p.getImports()) {
				Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
				Program current = (Program)resource.getContents().get(0);
				if(current.getFeatures() != null && current.getFeatures().getConfiguration() != null)
					configList = current.getFeatures().getConfiguration().getFeatureList();
			}
		for(Config conf : configList){
			Map<BigInteger, Set<Delta>> deltaMapLevel = auxiliary.deltaLevel(p, conf);
			for (BigInteger b : deltaMapLevel.keySet()) {
				Map<String, Set<ModifiesClass>> modifiesClassMap = new HashMap<String, Set<ModifiesClass>>();
				Set<String> className = new HashSet<String>();
				for (Delta d : deltaMapLevel.get(b))
					for (Classm cm : d.getClassesList())
						if (cm.getAction().equals("adds")) {
							if (!className.add(cm.getAdds().getClass_().getName()))
								if(p.getModulesList().contains((Module)d.eContainer()))
									error("Cannot add this class, it can create a conflict for configuration " + auxiliary.configurationToString(p, conf), cm.getAdds(), DJPackage.ADDS_CLASS);
						}
						else if (cm.getAction().equals("remove")) {
							if (!className.add(cm.getRemove().getClass_().getName()))
								if(p.getModulesList().contains((Module)d.eContainer()))
									error("Cannot remove this class, it can create a conflict for configuration " + auxiliary.configurationToString(p, conf), cm.getRemove(), DJPackage.REMOVE_CLASS);
						}	
						else if (cm.getAction().equals("modifies")) {
							String name = cm.getModifies().getClass_().getName();
							Set<ModifiesClass> modc = new HashSet<ModifiesClass>();
							if (modifiesClassMap.get(name) != null)
								modc.addAll(modifiesClassMap.get(name));
							modc.add(cm.getModifies());
							modifiesClassMap.put(name, modc);
							checkMethodConflict(modifiesClassMap, p, conf);
							checkFieldConflict(modifiesClassMap, p, conf);
						}
				for (String name : modifiesClassMap.keySet())
					if (className.contains(name))
						for (ModifiesClass mc : modifiesClassMap.get(name))
							if(p.getModulesList().contains(new  ContainingModuleFinded().lookup(mc)))
								error("Cannot modify this class, it can create a conflict for configuration " + auxiliary.configurationToString(p, conf), mc, Integer.valueOf(0));
			}	
		}
	}

	/*
	 * Questo metodo segnala gli errori di conflitto su classi modificate ad uno stesso livello dell'after-DAG 
	 * per quanto riguarda i metodi al loro interno.
	 */
	private void checkMethodConflict(Map<String, Set<ModifiesClass>> modifiesClassMap, Program p, Config conf) {
		if(deactivateValidator()) return;
		for (String name : modifiesClassMap.keySet()) {
			Set<String> methodName = new HashSet<String>();
			for (ModifiesClass mc : modifiesClassMap.get(name)) {
				Set<String> methodThisClass = new HashSet<String>();
				for (RemovesMethod rm : mc.getMethod().getRemoveList()) {
					if (!methodName.add(rm.getMethodRef().getName())) {
						error("Cannot remove this method, it can create a conflict for configuration " + auxiliary.configurationToString(p, conf), rm, Integer.valueOf(0));
						error("Cannot modify this class, it can create a conflict. Look at the method in the configuration " + auxiliary.configurationToString(p, conf), mc, Integer.valueOf(0));
					}
					else {
						methodThisClass.add(rm.getMethodRef().getName());
					}
				}
				for (ModifiesMethod mm : mc.getMethod().getModifiesList()) {
					if ((!methodName.add(mm.getMethodRef().getName())) && (!methodThisClass.contains(mm.getMethodRef().getName()))) {
						error("Cannot modifies this method, it can create a conflict", mm, Integer.valueOf(1));
						error("Cannot modifies this class, it can create a conflict look the method in the configuration " + auxiliary.configurationToString(p, conf), mc, Integer.valueOf(0));
					}
				}
				for (AddsMethod am : mc.getMethod().getAddsList())
					if ((!methodName.add(am.getMethod().getReference().getName())) && (!methodThisClass.contains(am.getMethod().getReference().getName()))) {
						error("Cannot add this method, it can create a conflict", am.getMethod(), Integer.valueOf(0));
						error("Cannot modify this class, it can create a conflict. Look at the method for configuration " + auxiliary.configurationToString(p, conf), mc, Integer.valueOf(0));
					}
					else {
						methodThisClass.add(am.getMethod().getReference().getName());
					}
			}
		}
	}
	
	/*
	 * Questo metodo segnala gli errori di conflitto su classi modificate ad uno stesso livello dell'after-DAG 
	 * per quanto riguarda i campi al loro interno.
	 */
	private void checkFieldConflict(Map<String, Set<ModifiesClass>> modifiesClassMap, Program p,Config conf) {
		if(deactivateValidator()) return;
		Set<String> fieldThisClass = new HashSet<String>();
		for (String name : modifiesClassMap.keySet()) {
			Set<String> fieldName = new HashSet<String>();
			for (ModifiesClass mc : modifiesClassMap.get(name)) {
				fieldThisClass.clear();
				for (RemovesField rf : mc.getField().getRemoveList()) {
					if (!fieldName.add(rf.getFieldRef().getName())) {
						error("Cannot remove this field, it can create a conflict for configuration " + auxiliary.configurationToString(p, conf), rf, Integer.valueOf(0));
						error("Cannot modify this class, it can create a conflict. Look at the field for configuration " + auxiliary.configurationToString(p, conf), mc, Integer.valueOf(0));
					}else {
						fieldThisClass.add(rf.getFieldRef().getName());
					}
				}
				for (AddsField af : mc.getField().getAddsList())
					if ((!fieldName.add(af.getField().getReference().getName())) && (!fieldThisClass.contains(af.getField().getReference().getName()))) {
						error("Cannot add this field, it can create a conflict for configuration " + auxiliary.configurationToString(p, conf), af.getField(), Integer.valueOf(0));
						error("Cannot modify this class, it can create a conflict. Look at the field for configuration " + auxiliary.configurationToString(p, conf), mc, Integer.valueOf(0));
					}else {
						fieldThisClass.add(af.getField().getReference().getName());
					}
			}
		}
	}

	/*
	 * Segnala errori sulle operazioni dei delta moduli sulle classi per ogni configurazione, indicando
	 * anche in quale configurazione � stato rilevato l'errore.
	 * Richiama i metodi sottostanti per ulteriori controlli.
	 */
	@Check
	public void checkApplicationDelta(Program p) {
		if(DJIdeProperties.getValidationStatus() != ValidationStatus.VALIDATE_ALL) return;
		
		try{
			Collection<Import> importList = p.getImports();
			Collection<Module> moduleList = new LinkedList<Module>();
			Collection<Config> configList = new LinkedList<Config>();
			Map<BigInteger, Set<Delta>> deltaMapLevel = new HashMap<BigInteger, Set<Delta>>();
			if(p.getFeatures() != null && p.getFeatures().getConfiguration() != null)
				configList = p.getFeatures().getConfiguration().getFeatureList();
			else
				for (Import imp : importList) {
					Resource resource = EcoreUtil2.getResource(p.eResource(), imp.getImportURI());
					Program current = (Program)resource.getContents().get(0);
					moduleList.addAll(current.getModulesList());
					if(current.getFeatures() != null && current.getFeatures().getConfiguration() != null)
						configList = current.getFeatures().getConfiguration().getFeatureList();
				}
			for(Config conf : configList){
				deltaMapLevel = auxiliary.deltaLevel(p, conf);  
				moduleList.addAll(p.getModulesList());
				Map<String, CST> classMapApply = new HashMap<String, CST>();
				Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
				for(Class c : (p2.getModulesList().get(0).getCore().getClassesList())){
					CST cn = new CST(c);
					if(c.getExtends() == null && !c.getName().equals("Object"))
						cn.setExtending("Object");
					classMapApply.put(c.getName(), cn);
				}
				for (Module m : moduleList){
					if (m.getNtype() != null)
						if (m.getNtype().equals("core"))
							for (Class c : m.getCore().getClassesList()) {
								CST cn = new CST(c);
								if(c.getExtends() == null)
									cn.setExtending("Object");
								classMapApply.put(c.getName(), cn);
							}
				}
				for (BigInteger b : deltaMapLevel.keySet())
					for (Delta d : deltaMapLevel.get(b)){
						Program pTemp = new ContainingProgramFinded().lookup((Module) d.eContainer());
						for (Classm cm : d.getClassesList())
							if (cm.getAction().equals("adds")) {
								Class c = cm.getAdds().getClass_();
								if (classMapApply.containsKey(c.getName())){
									if(p.equals(pTemp))
										error("Cannot add this class, it already exists for configuration " + auxiliary.configurationToString(p, conf), cm.getAdds().getClass_(), DJPackage.CLASS__NAME);
								}
								else{
									CST cn = new CST(c);
									if(c.getExtends() == null)
										cn.setExtending("Object");
									classMapApply.put(c.getName(), cn);
								}
							}
							else if (cm.getAction().equals("remove")) {
								Class c = cm.getRemove().getClass_();
								if (c != null && c.getName() != null && !classMapApply.containsKey(c.getName())){
									if(p.equals(pTemp))
										error("Cannot remove this class, it not exists for configuration " + auxiliary.configurationToString(p, conf), cm.getRemove(), DJPackage.REMOVE_CLASS);
								}else if(c!= null && c.getName() != null){
									classMapApply.remove(c.getName());
								}
							}
							//FIX ME XTEXT null-cheks added
							else if (cm != null && cm.getModifies() != null && cm.getAction() != null && cm.getAction().equals("modifies")) {
								Class c = cm.getModifies().getClass_();
								if (c != null && classMapApply != null && !classMapApply.containsKey(c.getName())){
									if(p.equals(pTemp))
										error("Cannot modify this class, it not exists for configuration " + auxiliary.configurationToString(p, conf), cm.getModifies(), DJPackage.MODIFIES_CLASS__CLASS);
								} 
								else
									applyModifies(classMapApply, cm.getModifies(), p, conf);
							}
					}
				checkExtends(classMapApply, p, conf);
				checkType(classMapApply, p, conf);
				checkConstructor(classMapApply, p, conf);	
			}
		} catch (Exception ecc) {
			ecc.printStackTrace();
		}
	}
	
	
	private void checkExtends(Map<String, CST> classMapApply, Program p, Config conf) {
		for(CST cst : classMapApply.values()){
			if(classMapApply.get(cst.getExtending()) == null){
				Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
				boolean trovato = false;
				for(Class c : p2.getModulesList().get(0).getCore().getClassesList())
					if(c.getName().equals(cst.getExtending())){
						System.err.println(cst.getExtending());
						trovato = true;
					}
				if(!trovato && !cst.getExtending().equals("")) {
					error("There is an error, this extending class doesn't exist in the configuration " + auxiliary.configurationToString(p, conf) + ", look the last extending modify ", cst.getClasse(), DJPackage.CLASS__EXTENDS);
				}
			}		
				
		}
	}
		
	
	/*
	 * Questo metodo controlla le operazioni svolte sulle classi modificate 
	 * (in una determinata configuarione) ed eventualmente ne segnala gli errori se vengono applicate 
	 * remove e/o modifies a metodi o campi che non esistono, ed add a metodi o campi giˆ esistenti 
	 */
	private void applyModifies(Map<String, CST> classMapApply, ModifiesClass mod, Program p, Config conf) {
		if(deactivateValidator()) return;
		try{
			if(mod == null || mod.getClass_() == null || mod.getClass_().getName() == null) return;
			Program pTemp = new ContainingProgramFinded().lookup(mod);
			CST cn = classMapApply.get(mod.getClass_().getName());
			Collection<String> removedList = new HashSet<String>();
			for (RemovesMethod rm : mod.getMethod().getRemoveList()){
				if (cn.containsMethod(rm.getMethodRef().getName()))
					removedList.add(rm.getMethodRef().getName());
				else if(pTemp.equals(p))
					error("Cannot remove this method, it not exists in this configuration for configuration " + auxiliary.configurationToString(p, conf), rm, Integer.valueOf(0));
			}
			for (ModifiesMethod mm : mod.getMethod().getModifiesList()) {
				if (!cn.containsMethod(mm.getMethodRef().getName()) && pTemp.equals(p))
					error("Cannot modify this method, it not exists in this configuration for configuration " + auxiliary.configurationToString(p, conf), mm, Integer.valueOf(1));
				else
					cn.addModifiesMethod(mm);
			}
			for (AddsMethod am : mod.getMethod().getAddsList()) {
				if (cn != null && am != null && am.getMethod() != null && am.getMethod().getReference() != null && !cn.containsMethod(am.getMethod().getReference().getName()))
					cn.addMethod(am.getMethod());
				else if (am != null && am.getMethod() != null && am.getMethod().getReference() != null && !removedList.contains(am.getMethod().getReference().getName()) && pTemp.equals(p))
					error("Cannot add this method, it already exists in this configuration for configuration " + auxiliary.configurationToString(p, conf), am.getMethod(), Integer.valueOf(1));
				else if (pTemp != null && pTemp.equals(p))
					error("Cannot add this method, it has been removed in this class. Use the modify operation for configuration " + auxiliary.configurationToString(p, conf), am.getMethod(), Integer.valueOf(1));
			}
			for (String name : removedList) {
				cn.removeModifiesMethod(name);
				cn.removeMethod(name);
		    }
			removedList.clear();
			for (RemovesField rf : mod.getField().getRemoveList()) {
				if (cn.containsField(rf.getFieldRef().getName()))
					removedList.add(rf.getFieldRef().getName());
				else if( pTemp.equals(p))
					error("Cannot remove this field, it doesn't exist in this configuration for configuration " + auxiliary.configurationToString(p, conf), rf, Integer.valueOf(0));
			}
			for (AddsField af : mod.getField().getAddsList()) {
				if (!cn.containsField(af.getField().getReference().getName()))
					cn.addField(af.getField());
				else if( pTemp.equals(p))
					error("Cannot add this field, it already exists in this configuration for configuration " + auxiliary.configurationToString(p, conf), af.getField(), Integer.valueOf(1));
			}
			for (String name : removedList)
				cn.removeField(name);
			removedList.clear();
			if(mod.getExtends() != null)
				cn.setExtending(mod.getExtends());
			if(mod.getConstructor() != null)
				//if(cn.getConstructor().size() != 0)
				cn.setConstructor(mod.getConstructor());
		}catch(Exception ex) {ex.printStackTrace();}
	}

	/*
	 * Questo metodo controlla i costruttori con tutti i suoi argomenti e la correttezza di tipo delle espressioni al suo interno
	 */
	private void checkConstructor(Map<String, CST> classMapApply, Program p, Config conf) {
		if(deactivateValidator()) return;
		try{
			for (String nameClass : classMapApply.keySet()) {
				CST cst = classMapApply.get(nameClass);
				Program pTemp = null;
				if(cst.getConstructor().size() == 0)
					pTemp = new ContainingProgramFinded().lookup(cst.getClasse());
				else
		        	pTemp = new ContainingProgramFinded().lookup(cst.getConstructor().get(0));
				if(cst.getConstructor().size() > 1  && pTemp.equals(p)){
					error("Cannot declare more than one costructor in a class", cst.getClasse(), DJPackage.CLASS__NAME);
				}
				else if(cst.getConstructor().size() == 0){
					if((!cst.getExtending().equals("Object") && classMapApply.get(cst.getExtending()).getConstructor().size() != 0))
						error("A constuctor must be declared because the superclass has a constructor declaration for the configuration " + auxiliary.configurationToString(p, conf) , cst.getClasse(), DJPackage.CLASS__NAME);
					else if(!classNotConstructor.isEmpty() && !classNotConstructor.contains(cst.getClasse().getName())){
						error("The constructor is declared only in some configurations, but not for configuration " + auxiliary.configurationToString(p, conf) , cst.getClasse(), DJPackage.CLASS__NAME);
					}
				}
				else if(!cst.getClasse().getName().equals("Object")){
					Constructor constructor = cst.getConstructor().get(0);
					if(classMapApply == null || cst == null || classMapApply.get(cst.getExtending()) == null || classMapApply.get(cst.getExtending()).getConstructor() == null);
					else if(classMapApply.get(cst.getExtending()).getConstructor().size() == 0 )//&& pTemp .equals(p))
						error("Error, you can not declare the constructor, the super class not have a constructor for configuration " + auxiliary.configurationToString(p, conf) , cst.getClasse(), DJPackage.CLASS__NAME);
					else{
						Constructor constructorParent = classMapApply.get(cst.getExtending()).getConstructor().get(0);
						int temp1 = cst.getFieldList().size();
						int temp2 = constructorParent.getParams().size();
						if((temp1 + temp2) != constructor.getParams().size() && pTemp != null && pTemp.equals(p)){
							error("Wrong number of parameters in the constructor declaration for configuration " + auxiliary.configurationToString(p, conf), constructor, DJPackage.CONSTRUCTOR);
						}
						if(constructor.getConstructorSuperExpression() != null ){
							if(temp2 != constructor.getConstructorSuperExpression().getParS().size())// && pTemp != null && pTemp.equals(p))
								error("Wrong number of parameters in the constructor declaration for the super constructor, in constructor declaration for configuration " + auxiliary.configurationToString(p, conf), constructor, DJPackage.CONSTRUCTOR);
							else {
								int cont = 0;
								String stringType = "";
								boolean error = false;
								for(Parameter par : constructor.getConstructorSuperExpression().getParS()){
									if(par.getType().getClassref() != null && classMapApply.get(par.getType().getClassref().getName()) == null){
										Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
										if(!p2.getModulesList().get(0).getCore().getClassesList().contains(par.getType().getClassref()))
											error("There is an error, this class doesn't exist in the configuration " + auxiliary.configurationToString(p, conf), par, DJPackage.PARAMETER);	
									}
									ClassType ct1 = new ClassType();
									ClassType ct2 = new ClassType();
									ct1.setType(par.getType());
									if(ct1.getBasicType() != null && !ct1.getBasicType().equals(""))
										stringType += ", " + ct1.getBasicType();
									else
										stringType += ", " + ct1.getClassType().getName();
									ct2.setType(constructorParent.getParams().get(cont).getType());
									if(!ct1.equals(ct2, classMapApply)){
										error = true;
									}
									cont++;
								}
								if(error)// && pTemp != null && pTemp.equals(p))
									error("The constructor " + nameClass + "(" + stringType.substring(2) + ")"+ " is undefined for configuration " + auxiliary.configurationToString(p, conf), constructor.getConstructorSuperExpression(), DJPackage.CONSTRUCTOR_SUPER_EXPRESSION);
							}
						}else if(temp2 != 0)
							error("super call needed for configuration " + auxiliary.configurationToString(p, conf), constructor, DJPackage.CONSTRUCTOR);
						if(temp1 != constructor.getConstructorFieldExpression().size() && pTemp != null && pTemp.equals(p)) {
							//error("Wrong number of parameters for configuration " + auxiliary.configurationToString(p, conf), constructor, DJPackage.CONSTRUCTOR);
							String nameF = "";
	                           for(Field f : cst.getFieldList())
	                               nameF += f.getReference().getName() + "  ";
	                           error("Wrong number of parameters " + nameF + "in the constructor declaration for configuration " + auxiliary.configurationToString(p, conf), constructor, DJPackage.CONSTRUCTOR);
						}
						else {
							for(ConstructorFieldExpression cfe : constructor.getConstructorFieldExpression()){
								Parameter par = cfe.getParT();
								if(par.getType().getClassref() != null && classMapApply.get(par.getType().getClassref().getName()) == null){
									Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
									if(!p2.getModulesList().get(0).getCore().getClassesList().contains(par.getType().getClassref()))
										error("There is an error, this class doesn't exist in the configuration " + auxiliary.configurationToString(p, conf), cfe, DJPackage.CONSTRUCTOR_FIELD_EXPRESSION);
								}
								ClassType ct1 = new ClassType();
								ClassType ct2 = new ClassType();
								String s1 = "";
								String s2 = "";
								if(par != null){
									ct1.setType(par.getType());
									if(ct1.getBasicType() != null && !ct1.getBasicType().equals(""))
										s1 = ct1.getBasicType();
									else if(ct1.getClassType() != null)
										s1 = ct1.getClassType().getName();
								}
								if(cfe.getField() != null){
									String name = cfe.getField().getName();
									ct2.setType(new CheckReturnType().checkTypeField(name, cst.getClasse()));
									if(ct2.getBasicType() != null && !ct2.getBasicType().equals(""))
										s2 = ct2.getBasicType();
									else if(ct2.getClassType() != null)
										s2 = ct2.getClassType().getName();
									else
										System.err.println("DJJavaValidator Error: " + name);
								}
								if(!ct1.equals(new ClassType()) && !ct2.equals(new ClassType()) && !ct1.equals(ct2, classMapApply)){// && pTemp != null  && pTemp.equals(p)){
									error("Type mismatch: cannot convert from " + s1 + "  to " + s2 +" for configuration " + auxiliary.configurationToString(p, conf), cfe, DJPackage.CONSTRUCTOR_FIELD_EXPRESSION);
								}
							}
						}
					}
				}
			}
		}catch(Exception ex) {ex.printStackTrace();}
	}
	
	/*
	 * Richiama il metodo sotto checkMethodType
	 */
	private void checkType(Map<String, CST> classMapApply, Program p, Config conf) {
		if(deactivateValidator()) return;
		try {
			for (String nameClass : classMapApply.keySet()) {
				CST cst = classMapApply.get(nameClass);
				for (Method method : cst.getMethodList()) {
					checkMethodType(classMapApply, method.getBody(), method.getReturntype(), nameClass, p, conf);
				}
				for (ModifiesMethod method : cst.getModifiesMethodList()){
					checkMethodType(classMapApply, method.getBody(), method.getReturntype(), nameClass, p, conf);
				} 
			}
		}
		catch (Exception ecc) {
			ecc.printStackTrace();
		}
	}

	/*
	 * Questo metodo controlla la correttezza del tipo di ritorno e delle assegnazioni e richiama
	 * il metodo sottostante checkExpression per controllare ogni espressione.
	 */
	private void checkMethodType(Map<String, CST> classMapApply, MethodBody body, Type returntype, String nameClass, Program p, Config conf) {
		if(deactivateValidator()) return;
		try {
			CheckReturnType checkType = new CheckReturnType();
			if (body == null)
				return;
			Expression ex = body.getExpressionReturn();
			Program pTemp = new ContainingProgramFinded().lookup(body);
			ClassType type = null;
			if(returntype.getBasic() != null && returntype.getBasic().equals("void")){
				if (ex != null && pTemp.equals(p))
					error("Void methods cannot return a value for configuration " + auxiliary.configurationToString(p, conf), ex, DJPackage.EXPRESSION);
				
			}else if(returntype.getClassref() != null){
				ClassType ctTemp = new ClassType();
				ctTemp.setType(returntype);
				if(classMapApply.get(ctTemp.getClassType().getName()) == null){
					Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
					if(!p2.getModulesList().get(0).getCore().getClassesList().contains(ctTemp.getClassType()))
						error("There is an error, this class doesn't exist in this configuration " + auxiliary.configurationToString(p, conf), returntype, DJPackage.EXPRESSION);
				}
			}else if ((body.getReturn() == null) || (ex == null)) {
				
				if (((returntype.getBasic() == null) || (!returntype.getBasic().equals("void"))) && pTemp.equals(p) ) {
					error("Cannot return null value or not return a value for configuration " + auxiliary.configurationToString(p, conf), returntype, DJPackage.TYPE);
				}
			}
			else if (ex.getValue() != null && pTemp.equals(p)){
				error("Cannot have an assignment in the return expression for configuration " + auxiliary.configurationToString(p, conf), body.getExpressionReturn(), DJPackage.EXPRESSION);
			}    	
			else if (ex.getTerminalExpression() != null) {
				TerminalExpression te = ex.getTerminalExpression();
				type = checkType.returnTypeTerminalExpression(te);
				if(type.getBasicType() == null && type.getClassType() == null  && pTemp.equals(p))
					error("Cannot return this value, there is an error in the return type for configuration " + auxiliary.configurationToString(p, conf), te, DJPackage.TERMINAL_EXPRESSION);
			}
			else if (ex.getMessage() != null){
				type = new ClassType();
				type = (checkType.returnTypeMessage(ex));
				if (type.getBasicType() == null && type.getClassType() == null && pTemp.equals(p)){
					error("Cannot use this expression for configuration " + auxiliary.configurationToString(p, conf), ex, DJPackage.EXPRESSION);
				}
			}
			if(type != null && !type.equals(returntype, classMapApply)  && pTemp.equals(p)){
				String s1 = type.getBasicType();
				if(s1 == null)
					s1 = type.getClassType().getName();
				String s2 = returntype.getBasic();
				if(s2 == null)
					s2 = returntype.getClassref().getName();
				error("Type mismatch: cannot convert from " + s1 + "  to " + s2 + " for configuration " + auxiliary.configurationToString(p, conf), ex, DJPackage.EXPRESSION);
			} 
			if (type != null) {
							
				typeExpression(ex, classMapApply, p);
			}
			ClassType ctTemp = new ClassType();
			if(ex != null)
				ctTemp = new CheckReturnType().returnTypeMessage(ex);
			if(ctTemp != null && ctTemp.getClassType() != null && classMapApply.get(ctTemp.getClassType().getName()) == null){
				Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
				if(!p2.getModulesList().get(0).getCore().getClassesList().contains(ctTemp.getClassType()))
					error("There is an error, this class doesn't exist for configuration " + auxiliary.configurationToString(p, conf), ex, DJPackage.EXPRESSION);
			}
			for (Expression expression : body.getExpressions()) {
				ClassType ct = checkType.returnTypeMessage(expression);
				if(expression.getTerminalExpression() != null)
					if(expression.getTerminalExpression().getCast() != null)
						typeExpression(expression.getTerminalExpression().getCast().getExpression(), classMapApply, p);
					else if((expression.getTerminalExpression().getString() != null || 
							expression.getTerminalExpression().getInt() != null || 
							expression.getTerminalExpression().getNull() != null) && pTemp.equals(p))
						error("The left-hand side of an assignment must be a variable for configuration " + auxiliary.configurationToString(p, conf),expression, DJPackage.EXPRESSION);
				typeExpression(expression, classMapApply, p);
				if(ct.getClassType() == null && ct.getBasicType() == null && pTemp.equals(p))
					error("Cannot use this expression", expression, DJPackage.EXPRESSION);
				if (expression.getValue() != null) {
					if(expression.getMessage() != null && expression.getMessage().getMethodCall() != null && pTemp.equals(p))
						error("The left-hand side of an assignment must be a variable for configuration " + auxiliary.configurationToString(p, conf), expression, DJPackage.EXPRESSION);
					ClassType ctValue = checkType.returnTypeMessage(expression.getValue());
					if(expression.getValue().getTerminalExpression() != null && expression.getValue().getTerminalExpression().getCast() != null)
						typeExpression(expression.getValue().getTerminalExpression().getCast().getExpression(), classMapApply, p);
					typeExpression(expression.getValue(), classMapApply, p);
					if(ctValue.getClassType() == null && ctValue.getBasicType() == null && pTemp.equals(p))
						error("Cannot use this expression for configuration " + auxiliary.configurationToString(p, conf), expression.getValue(), DJPackage.EXPRESSION);
					if(!ctValue.equals(ct, classMapApply) && pTemp.equals(p)){
						String s1 = ctValue.getBasicType();
						if(s1 == null && ctValue.getClassType() != null)
							s1 = ctValue.getClassType().getName();
						String s2 = ct.getBasicType();
						if(s2 == null && ct.getClassType() != null)
							s2 = ct.getClassType().getName();
						error("Type mismatch: cannot convert from " + s1 + "  to " + s2 + " for configuration " + auxiliary.configurationToString(p, conf), expression, DJPackage.EXPRESSION);
					} 	
				}
			}
		}catch (Exception ecc) {
			ecc.printStackTrace();
		}
	}

	/*
	 * Questo metodo fa i controlli di tipo e ne segnala i possibili errori. 
	 */
	private void typeExpression(Expression expression, Map<String, CST> classMapApply, Program p) {
		if(deactivateValidator()) return;
		try {
			Program pTemp = new ContainingProgramFinded().lookup(expression);
			Expression expr = null;
			boolean receiver = false;
			while(expression != null){
				ClassType type = null;
				if (expression.getReceiver() != null) {
					expr = expression.getReceiver();
					receiver = true;
				} else 
					expr = expression;
				if (expr.getTerminalExpression() == null) {
					type = new CheckReturnType().returnTypeMessage(expr);
					if (expr != null && expr.getMessage() != null && expr.getMessage().getFieldAccess() != null){
						if (type != null) {
							if (type.getClassType() != null)
								if (classMapApply.get(type.getClassType().getName()) == null && pTemp.equals(p)) 
									error("This class doesn't exists in this configuration", expression, Integer.valueOf(31));
								//FIX ME XTEXT null-checks added
								else if (expression != null && expression.getMessage() != null && expression.getMessage().getMethodCall() != null &&
										 expression.getMessage().getMethodCall() != null && pTemp.equals(p)) {
									if (!classMapApply.get(type.getClassType().getName()).containsMethod(expression.getMessage().getMethodCall().getName().getName()) && pTemp.equals(p))
										error("This method doesn't exists in this configuration", expression.getMessage().getMethodCall(), DJPackage.METHOD_CALL__NAME);
									for (Argument arg : expression.getMessage().getMethodCall().getArgs())
										typeExpression(arg.getExpression(), classMapApply, p);
								} else if (expression != null && expression.getMessage() != null && (expression.getMessage().getFieldAccess() != null) && 
										(!classMapApply.get(type.getClassType().getName()).containsField(expression.getMessage().getFieldAccess().getName().getName())) && pTemp.equals(p)) {
									error("This field doesn't exists in this configuration", expression.getMessage().getFieldAccess(), DJPackage.FIELD_ACCESS__NAME);
								}
						}else if(pTemp.equals(p))
							error("This object doesn't exist", expression, Integer.valueOf(31));
					}
					else if (expr != null && expr.getMessage() != null && expr.getMessage().getMethodCall() != null)
						if (type != null) {
							if (type.getClassType() != null)
								if (classMapApply.get(type.getClassType().getName()) == null && pTemp.equals(p)) 
									error("This class doesn't exist in this configuration", expression, Integer.valueOf(31));
								else if (expression.getMessage().getMethodCall() != null) {
									if (!classMapApply.get(type.getClassType().getName()).containsMethod(expression.getMessage().getMethodCall().getName().getName()) && pTemp.equals(p))
										error("This method doesn't exist in this configuration", expression.getMessage().getMethodCall(), DJPackage.METHOD_CALL__NAME);
									for (Argument arg : expression.getMessage().getMethodCall().getArgs())
										typeExpression(arg.getExpression(), classMapApply, p);
								}else if ((expression.getMessage().getFieldAccess() != null) && 
										(!classMapApply.get(type.getClassType().getName()).containsField(expression.getMessage().getFieldAccess().getName().getName())) && pTemp.equals(p)) {
									error("This field not exist in this configuration", expression.getMessage().getFieldAccess(), DJPackage.FIELD_ACCESS__NAME);
								}
						}else if(pTemp.equals(p))
							error("There is an error, this object doesn't exist", expression, Integer.valueOf(31));
				}else {
					ClassType temp = new ClassType();
					temp = new CheckReturnType().returnTypeMessage(expr);
					if (expr.getTerminalExpression().getCast() != null) {
						if (expr.getTerminalExpression().getCast().getExpression().getValue() != null && pTemp.equals(p))
							error("Cannot have an assignment in this expression", expression, Integer.valueOf(31));
						typeExpression(expr.getTerminalExpression().getCast().getExpression(), classMapApply, p);
						ClassType temp2 = new ClassType();
						Expression tempEx = expr.getTerminalExpression().getCast().getExpression();
						temp2 = new CheckReturnType().returnTypeMessage(tempEx);
						if(tempEx.getTerminalExpression() == null);
						else if (tempEx.getTerminalExpression().getNew() != null) {
							if(!checkConstructorCall(tempEx.getTerminalExpression().getNew(), classMapApply, p) && pTemp.equals(p))
								error("Error in constructor call", tempEx.getTerminalExpression(), DJPackage.TERMINAL_EXPRESSION);
						}else if (tempEx.getTerminalExpression().getOriginal() != null) {
							ModifiesMethod originalMethod = new ContainingModifiesMethodFinded().lookup(tempEx.getTerminalExpression().getOriginal());
							if (originalMethod == null)
								error("Cannot use this expression, an original method not exists", expression, Integer.valueOf(31));
							else
								if(originalMethod.getParams().size() == tempEx.getTerminalExpression().getOriginal().getPar().size()){
									int c = 0;
									List<Parameter> par = tempEx.getTerminalExpression().getOriginal().getPar();
									for(Parameter param : originalMethod.getParams()){
										ClassType ctTemp1 = new ClassType();
										ctTemp1.setType(par.get(c++).getType());
										ClassType ctTemp2 = new ClassType();
										ctTemp2.setType(param.getType());
										if(!ctTemp1.equals(ctTemp2, classMapApply)){
											error("There is an error, look the type of the argument of original method call ", tempEx.getTerminalExpression(), DJPackage.EXPRESSION);
											break;
										}
									}
								}
								else
									error("There is an error, look the argument of original method call", tempEx, DJPackage.EXPRESSION);
						}
						if (((temp2 == null) || ((!temp2.equals(temp, classMapApply)) && (!temp.equals(temp2, classMapApply))))  && pTemp.equals(p))
							error("Error in cast, this is a stupid cast", expression.getTerminalExpression().getCast(), Integer.valueOf(39));
					}
					else if (expr.getTerminalExpression().getNew() != null) {
						if(!checkConstructorCall(expr.getTerminalExpression().getNew(), classMapApply, p) && pTemp.equals(p))
							error("The constructor " + expr.getTerminalExpression().getNew().getType().getName() +  " is undefined with this argument", expr.getTerminalExpression(), DJPackage.TERMINAL_EXPRESSION);
					}
					else if (expr.getTerminalExpression().getOriginal() != null){
						ModifiesMethod originalMethod = new ContainingModifiesMethodFinded().lookup(expr.getTerminalExpression().getOriginal());
						if (originalMethod == null)
							error("Cannot use this expression, an original method not exists", expression, Integer.valueOf(31));
						else
							if(originalMethod.getParams().size() == expr.getTerminalExpression().getOriginal().getPar().size()){
								int c = 0;
								List<Parameter> par = expr.getTerminalExpression().getOriginal().getPar();
								for(Parameter param : originalMethod.getParams()){
									ClassType ctTemp1 = new ClassType();
									ctTemp1.setType(par.get(c++).getType());
									ClassType ctTemp2 = new ClassType();
									ctTemp2.setType(param.getType());
									if(!ctTemp1.equals(ctTemp2, classMapApply)){
										error("There is an error, look the type of the argument of original method call ", expr.getTerminalExpression(), DJPackage.EXPRESSION);
										break;
									}
								}
							}
							else
								error("There is an error, look the argument of original method call", expr, DJPackage.EXPRESSION);
					
					}
					if(receiver)
						if(temp.getClassType() == null)
							error("There is an error, class type expected", expr, DJPackage.EXPRESSION);
						else
							type = temp;
				}
				if (type != null && type.getClassType() != null){
					if (classMapApply.get(type.getClassType().getName()) == null){
						Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
						if(!p2.getModulesList().get(0).getCore().getClassesList().contains(type) && pTemp.equals(p))
							error("There is an error, this class doesn't exist in this configuration", expression, Integer.valueOf(31));
					}else if (expression.getMessage() != null && (expression.getMessage().getMethodCall() != null)){
						if (!classMapApply.get(type.getClassType().getName()).containsMethod(expression.getMessage().getMethodCall().getName().getName()) && pTemp.equals(p))
							error("There is an error, this method doesn't exist in this configuration", expression, Integer.valueOf(31));
						if (expression.getMessage().getMethodCall().getArgs() != null) {
							int nArgMetCall = expression.getMessage().getMethodCall().getArgs().size();
							int nArg = 0;
							boolean trovato = false;
							for (Method method : classMapApply.get(type.getClassType().getName()).getMethodList()){
								if (method.getReference().getName().equals(expression.getMessage().getMethodCall().getName().getName())){
									trovato = true;
									nArg = method.getParams().size();
								}
							}
							if(!trovato)
								for (ModifiesMethod method : classMapApply.get(type.getClassType().getName()).getModifiesMethodList()){
									if (method.getMethodRef().getName().equals(expression.getMessage().getMethodCall().getName().getName())){
										nArg = method.getParams().size();
									}
								}
							if (nArgMetCall != nArg) {
								for (Argument arg : expression.getMessage().getMethodCall().getArgs()) {
									typeExpression(arg.getExpression(), classMapApply, p);
								}
								if(pTemp != null && pTemp.equals(p) && pTemp.equals(p))
									error("There is an error, look the argument of method call", expression, Integer.valueOf(31));
							} else {
								int i = 0;
								for (Argument arg : expression.getMessage().getMethodCall().getArgs()) {
									typeExpression(arg.getExpression(), classMapApply, p);
									ClassType typeArg = new ClassType();
									typeArg = new CheckReturnType().returnTypeMessage(arg.getExpression());
									for (Method method : classMapApply.get(type.getClassType().getName()).getMethodList())
										if (method.getReference().getName().equals(expression.getMessage().getMethodCall().getName().getName())) {
											Parameter par = (Parameter)method.getParams().get(i++);
											ClassType typePar = new ClassType();
											typePar.setType(par.getType());
											if(typePar != null && !typeArg.equals(typePar, classMapApply) && pTemp.equals(p)){
												error("There is an error, look the type of the argument of method call ", arg.getExpression(), Integer.valueOf(31));
											}
										}
								}
							}
						}
					} else if (expression.getMessage() != null && (expression.getMessage().getFieldAccess() != null) && 
							(!classMapApply.get(type.getClassType().getName()).containsField(expression.getMessage().getFieldAccess().getName().getName())) && pTemp.equals(p)) {
						error("This field doesn't exist in this configuration", expression, Integer.valueOf(31));
					}
				}
				ClassType ctTemp = new ClassType();
				ctTemp = new CheckReturnType().returnTypeMessage(expression);
				if(ctTemp != null && ctTemp.getClassType() != null)
					if(classMapApply.get(ctTemp.getClassType().getName()) == null){
						Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
						if(!p2.getModulesList().get(0).getCore().getClassesList().contains(ctTemp.getClassType()))
								error("There is an error, this class doesn't exist in this configuration", expression, Integer.valueOf(31));
					}
				expression = expression.getReceiver();
			}
		} catch (Exception ecc) {
			ecc.printStackTrace();
		}
	}

  /*
   * Questo metodo viene utilizzato da typeExpression restituisce false nel caso ci siano errori 
   * nella chiamata del costruttore (nella new).
   */
	private boolean checkConstructorCall(New consCall, Map<String, CST> classMapApply, Program p) {
		if(deactivateValidator()) return true;
		if(consCall.getType() == null)
			return true;
		if(classMapApply.get(consCall.getType().getName()) == null){ 
			return true;
		}
		for(Constructor cons : classMapApply.get(consCall.getType().getName()).getConstructor()){
			int a = 0;
			boolean correct = false;
			if(consCall.getArgs().size() == cons.getParams().size()){
				correct = true;
				for(Argument arg : consCall.getArgs()){
					Parameter par = cons.getParams().get(a++);
					typeExpression(arg.getExpression(), classMapApply, p);
					ClassType typeArg = new ClassType();
					ClassType typePar = new ClassType();
					typeArg = new CheckReturnType().returnTypeMessage(arg.getExpression());
					typePar.setType(par.getType());
					if(typePar != null && !typeArg.equals(typePar, classMapApply)){
						correct = false;
						break;
					}
					if(typePar.getClassType() != null && classMapApply.get(typePar.getClassType().getName()) == null){
						Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
						if(!p2.getModulesList().get(0).getCore().getClassesList().contains(typePar.getClassType())){
							Program pTemp = new ContainingProgramFinded().lookup(par);
							if(p.equals(pTemp))
								error("There is an error, this class doesn't exist for some configuration", par, DJPackage.PARAMETER);
						}
					}
					if(typeArg.getClassType() != null && classMapApply.get(typeArg.getClassType().getName()) == null){
						Program p2 = (Program)DjResourceFactory.getSystemResource().getContents().get(0);
						if(!p2.getModulesList().get(0).getCore().getClassesList().contains(typeArg.getClassType())){
							Program pTemp = new ContainingProgramFinded().lookup(arg);
							if(p.equals(pTemp))
								error("There is an error, this class doesn't exist for some configuration", arg, DJPackage.ARGUMENT);
						}
					}
				}
			}
			if(correct)
				return true;
		}
		if(classMapApply.get(consCall.getType().getName()).getConstructor().size() == 0)
			return (consCall.getArgs().size() == 0);
		return false;
	}
	
	private boolean deactivateValidator() {
		return DJIdeProperties.getValidationStatus() == ValidationStatus.SYNTAX_ONLY;
	}
}